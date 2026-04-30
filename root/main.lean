import Definitions
theorem root : ∀ n : ℕ, ∃ p : ℕ, p > n ∧ Nat.Prime p := by
  intro n
  use (Nat.factorial n + 1).minFac
  have hge : Nat.factorial n + 1 ≠ 1 := by
    have := Nat.factorial_pos n; omega
  have hp : Nat.Prime (Nat.factorial n + 1).minFac := Nat.minFac_prime hge
  refine ⟨?_, hp⟩
  by_contra hle
  push_neg at hle
  have hdvd : (Nat.factorial n + 1).minFac ∣ Nat.factorial n + 1 := Nat.minFac_dvd _
  have hdvdfact : (Nat.factorial n + 1).minFac ∣ Nat.factorial n :=
    Nat.dvd_factorial hp.pos hle
  have hdvd1 : (Nat.factorial n + 1).minFac ∣ 1 := by
    have h := Nat.dvd_sub' hdvd hdvdfact
    have heq : Nat.factorial n + 1 - Nat.factorial n = 1 := by omega
    rwa [heq] at h
  have := hp.two_le
  have := Nat.le_of_dvd one_pos hdvd1
  omega