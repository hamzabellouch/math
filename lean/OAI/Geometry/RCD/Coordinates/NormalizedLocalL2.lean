import OAI.Geometry.RCD.Harmonic.LocalAffineMoments

namespace OAI

/-! # The normalized local L² norm and its actual integral -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] in
theorem l2_norm_sq_eq_integral (s : Set X) (f : Lp ℝ 2 (μ.restrict s)) :
    ‖f‖ ^ 2 = ∫ x in s, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq, sq_abs]

omit [MetricSpace X] in
/-- This identifies the normalization with the usual mean square,
including the zero-measure convention. -/
theorem normalizeLocalL2_norm_sq (s : Set X) (hfin : μ s ≠ ∞)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖normalizeLocalL2 μ s hfin f‖ ^ 2 =
      (μ.real s)⁻¹ * ∫ x in s, (f x) ^ 2 ∂μ := by
  rw [normalizeLocalL2, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, mul_pow,
    inv_pow, restrictedOne_norm, Real.sq_sqrt (by positivity : 0 ≤ μ.real s),
    l2_norm_sq_eq_integral]

theorem normalized_sobolev_mean_sq (s : Set X) (hfin : μ s ≠ ∞)
    (w : SobolevSpace μ hQ) :
    ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖ ^ 2 =
      (μ.real s)⁻¹ * ∫ x in s, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ := by
  rw [normalizeLocalL2_norm_sq]
  congr 1
  apply integral_congr_ae
  filter_upwards [SobolevSpace.restrictLp_coe μ hQ s w] with x hx
  rw [hx]

/-- A normalized harmonic function has mean square at most one, with no
pointwise value bound assumed. -/
theorem sobolev_mean_sq_le_one_of_normalized (s : Set X) (hfin : μ s ≠ ∞)
    (w : SobolevSpace μ hQ)
    (h : ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖ ≤ 1) :
    (μ.real s)⁻¹ * ∫ x in s, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ ≤ 1 := by
  rw [← normalized_sobolev_mean_sq μ hQ s hfin w]
  nlinarith [norm_nonneg (normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w))]

end RegularPointCoordinates

end

end OAI
