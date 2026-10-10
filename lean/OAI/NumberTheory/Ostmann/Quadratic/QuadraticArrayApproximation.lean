import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessCover
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMomentMean

namespace OAI

/-! # The fixed array approximates the original Jacobi statistic -/

namespace Ostmann

open scoped BigOperators

noncomputable def quadraticArrayStatistic (S : Finset ℕ) (M : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ s : S, rootNormalizedCoefficient F s * (realJacobi s.val M : ℂ)

theorem rootNormalizedCoefficient_sub (F G : ℕ → ℂ) (s : ℕ) :
    rootNormalizedCoefficient F s - rootNormalizedCoefficient G s =
      rootNormalizedCoefficient (fun s => F s - G s) s := by
  simp only [rootNormalizedCoefficient, mul_sub]

theorem quadraticArrayStatistic_sub_bound (S : Finset ℕ) (M : ℕ) (F G : ℕ → ℂ)
    (δ : ℝ) (hS : ∀ s ∈ S, 0 < s)
    (hFG : ∀ s ∈ S, ‖F s - G s‖ ≤ δ) :
    ‖quadraticArrayStatistic S M F - quadraticArrayStatistic S M G‖ ≤ S.card * δ := by
  unfold quadraticArrayStatistic
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s : S, δ := by
      apply Finset.sum_le_sum
      intro s _
      rw [← sub_mul, norm_mul, rootNormalizedCoefficient_sub,
        Complex.norm_real, Real.norm_eq_abs]
      have hroot := (rootNormalizedCoefficient_norm_le (fun s => F s - G s)
        s.val (hS s.val s.property)).trans (hFG s.val s.property)
      exact (mul_le_of_le_one_right (norm_nonneg _) (realJacobi_abs_le s.val M)).trans hroot
    _ = _ := by simp

theorem quadraticArrayStatistic_grid_error (T : ℝ) (S : Finset ℕ) (M : ℕ)
    (F G : ℕ → ℂ) (hS : ∀ s ∈ S, 0 < s) (hcard : (S.card : ℝ) ≤ Real.exp (14 * T))
    (hFG : ∀ s ∈ S, ‖F s - G s‖ ≤ Real.exp (-127 * T)) :
    ‖quadraticArrayStatistic S M F - quadraticArrayStatistic S M G‖ ≤ Real.exp (-113 * T) := by
  apply (quadraticArrayStatistic_sub_bound S M F G _ hS hFG).trans
  calc
    _ ≤ Real.exp (14 * T) * Real.exp (-127 * T) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem quadraticArrayStatistic_mean_of_moment (P S : Finset ℕ) (k l : ℕ)
    {I : Type*} (F : I → ℕ → ℂ) (pick : ℕ → I) (B : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hl : 0 < l) (hB : 0 ≤ B)
    (hm : (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (F (pick m))‖ ^ (2 * l)) ≤ B ^ (2 * l)) :
    (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (F (pick m))‖) ≤ B :=
  prime_product_mean_le_of_moment P k (2 * l) _ B hP hB (by omega) hm

end Ostmann

end OAI
