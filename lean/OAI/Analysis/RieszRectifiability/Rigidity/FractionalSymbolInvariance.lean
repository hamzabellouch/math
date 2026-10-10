import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSymbolBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric
open scoped RealInnerProductSpace

theorem fractionalSymbolKernel_isometry {d : ℕ} (m : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (ξ h : Ambient d) :
    fractionalSymbolKernel m (U ξ) (U h) = fractionalSymbolKernel m ξ h := by
  simp only [fractionalSymbolKernel, inverseDistancePow, dist_zero_left, U.norm_map, U.inner_map_map]

theorem fractionalSymbol_isometry (p : ℕ)
    (U : Ambient (p + 1) ≃ₗᵢ[ℝ] Ambient (p + 1)) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (U ξ) = fractionalSymbol p ξ := by
  have h := U.measurePreserving.integral_comp U.toMeasurableEquiv.measurableEmbedding
    (fractionalSymbolKernel (p + 1) (U ξ))
  simpa only [fractionalSymbolKernel_isometry, fractionalSymbol] using! h.symm

theorem fractionalSymbolKernel_smul_pos {d : ℕ} (m : ℕ) (t : ℝ) (ht : 0 < t)
    (ξ h : Ambient d) :
    fractionalSymbolKernel m (t • ξ) h = t ^ (m + 1) * fractionalSymbolKernel m ξ (t • h) := by
  by_cases hh : h = 0
  · subst h
    simp [fractionalSymbolKernel, inverseDistancePow]
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    unfold fractionalSymbolKernel inverseDistancePow
    simp only [dist_zero_left, norm_smul, Real.norm_of_nonneg ht.le,
      real_inner_smul_left, real_inner_smul_right, mul_pow]
    field_simp

theorem fractionalSymbol_smul_pos (p : ℕ) (t : ℝ) (ht : 0 < t) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (t • ξ) = t * fractionalSymbol p ξ := by
  have heq : fractionalSymbolKernel (p + 1) (t • ξ) = fun h =>
      t ^ (p + 1 + 1) * fractionalSymbolKernel (p + 1) ξ (t • h) :=
    funext (fractionalSymbolKernel_smul_pos (p + 1) t ht ξ)
  unfold fractionalSymbol
  rw [heq, integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure (Ambient (p + 1)))
      (fractionalSymbolKernel (p + 1) ξ) t (hR := ht.le)]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_succ]
  field_simp

theorem fractionalSymbol_smul_nonneg (p : ℕ) (t : ℝ) (ht : 0 ≤ t) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (t • ξ) = t * fractionalSymbol p ξ := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_smul, fractionalSymbol_zero, zero_mul]
  · exact fractionalSymbol_smul_pos p t h ξ

theorem fractionalSymbol_eq_unit_mul_norm (p : ℕ) (v : Ambient (p + 1)) (hv : ‖v‖ = 1)
    (ξ : Ambient (p + 1)) : fractionalSymbol p ξ = fractionalSymbol p v * ‖ξ‖ := by
  let U : Ambient (p + 1) ≃ₗᵢ[ℝ] Ambient (p + 1) :=
    Submodule.reflection (ℝ ∙ (ξ - ‖ξ‖ • v))ᗮ
  have hn : ‖ξ‖ = ‖‖ξ‖ • v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg ξ), hv, mul_one]
  have hU : U ξ = ‖ξ‖ • v := Submodule.reflection_sub hn
  calc
    _ = fractionalSymbol p (U ξ) := (fractionalSymbol_isometry p U ξ).symm
    _ = fractionalSymbol p (‖ξ‖ • v) := congrArg (fractionalSymbol p) hU
    _ = ‖ξ‖ * fractionalSymbol p v := fractionalSymbol_smul_nonneg p ‖ξ‖ (norm_nonneg ξ) v
    _ = _ := mul_comm _ _

end

end RieszRectifiability

end OAI
