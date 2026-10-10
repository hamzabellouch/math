import OAI.NumberTheory.Ostmann.Preliminaries.OccupiedResidueCollision

namespace OAI

/-! # The reciprocal-support Cauchy estimate in Elsholtz's size argument -/

namespace Ostmann

open scoped Classical BigOperators

 theorem reciprocal_sum_cauchy {ι : Type*} (P : Finset ι) (v : ι → ℝ)
    (hv : ∀ p ∈ P, 0 < v p) :
    (P.card : ℝ) ^ 2 ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, 1 / v p := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => Real.sqrt (v p)) (fun p => (Real.sqrt (v p))⁻¹)
  have hprod : (∑ p ∈ P, Real.sqrt (v p) * (Real.sqrt (v p))⁻¹) = (P.card : ℝ) := by
    calc
      _ = ∑ _p ∈ P, (1 : ℝ) := Finset.sum_congr rfl (fun p hp => mul_inv_cancel₀
        (Real.sqrt_pos.mpr (hv p hp)).ne')
      _ = _ := by simp
  have hs : (∑ p ∈ P, Real.sqrt (v p) ^ 2) = ∑ p ∈ P, v p :=
    Finset.sum_congr rfl (fun p hp => Real.sq_sqrt (hv p hp).le)
  have hi : (∑ p ∈ P, (Real.sqrt (v p))⁻¹ ^ 2) = ∑ p ∈ P, 1 / v p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [inv_pow, Real.sq_sqrt (hv p hp).le, one_div]
  rwa [hprod, hs, hi] at hc

 theorem occupied_support_cauchy (B : Set ℕ) (hB : B.Nonempty) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (Q K ell : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hell : 0 ≤ ell) (hpQ : ∀ p ∈ P, (p : ℝ) ≤ Q)
    (hlog : ∀ p ∈ P, ell ≤ Real.log (p : ℝ))
    (hsieve : (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤ K) :
    ell * (P.card : ℝ) ^ 2 ≤ Q * K *
      ∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues B p).card : ℝ) := by
  let v : ℕ → ℝ := fun p => (occupiedResidues B p).card
  have hv : ∀ p ∈ P, 0 < v p := by
    intro p hp
    dsimp [v]
    exact_mod_cast (occupiedResidues_nonempty hB (hP p hp).pos).card_pos
  have hvc : (∑ p ∈ P, v p) ≤ Q * K := by
    calc
      _ ≤ ∑ p ∈ P, Q * (v p / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        rw [← mul_div_assoc]
        exact (le_div_iff₀ hp').mpr (by nlinarith [hv p hp, hpQ p hp])
      _ = Q * (∑ p ∈ P, v p / p) := (Finset.mul_sum _ _ _).symm
      _ ≤ Q * K := mul_le_mul_of_nonneg_left hsieve hQ
  have hinv : 0 ≤ ∑ p ∈ P, 1 / v p :=
    Finset.sum_nonneg (fun p hp => div_nonneg zero_le_one (hv p hp).le)
  have hweight : ell * (∑ p ∈ P, 1 / v p) ≤
      ∑ p ∈ P, Real.log (p : ℝ) / v p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hlog p hp) (hv p hp).le
  calc
    _ ≤ ell * ((∑ p ∈ P, v p) * ∑ p ∈ P, 1 / v p) :=
      mul_le_mul_of_nonneg_left (reciprocal_sum_cauchy P v hv) hell
    _ ≤ ell * ((Q * K) * ∑ p ∈ P, 1 / v p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvc hinv) hell
    _ = Q * K * (ell * ∑ p ∈ P, 1 / v p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (mul_nonneg hQ hK)

end Ostmann

end OAI
