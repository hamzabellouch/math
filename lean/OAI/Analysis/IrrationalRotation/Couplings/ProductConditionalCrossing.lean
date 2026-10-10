import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalKernels
import OAI.Analysis.IrrationalRotation.Product.OneCoordinateCrossing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling CouplingMarginalBounds

theorem right_condDistrib_crossing_lower (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → x i < u →
      ENNReal.ofReal (rho (P.κ i) (P.m i) w) / 10 ≤
        condDistrib rightEndpoint leftEndpoint (law P) x
          {y : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [right_condDistrib_coordinate_law P, ae_leftEndpoint_mem_unit P]
    with x hx hxunit i w u hw _hu0 hu1 hxu
  have hevent : {y : Endpoint | x i < u ∧ u ≤ y i} =
      (fun y : Endpoint => y i) ⁻¹' Ici u := by
    ext y
    simp [hxu]
  rw [hevent, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Ici, hx i]
  exact rightGivenLeft_crossing_lower (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i) hw (hxunit i).1 hxu hu1

theorem left_condDistrib_crossing_lower (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → u ≤ y i →
      ENNReal.ofReal (rho (P.κ i) (P.m i) w) / 10 ≤
        condDistrib leftEndpoint rightEndpoint (law P) y
          {x : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [left_condDistrib_coordinate_law P, ae_rightEndpoint_mem_unit P]
    with y hy hyunit i w u hw hu0 _hu1 huy
  have hevent : {x : Endpoint | x i < u ∧ u ≤ y i} =
      (fun x : Endpoint => x i) ⁻¹' Iio u := by
    ext x
    simp [huy]
  rw [hevent, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio, hy i]
  exact leftGivenRight_crossing_lower (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
    (P.t_nonneg i) (P.t_le i) hw (hyunit i).2 huy hu0

theorem right_condDistrib_crossing_real_lower (P : Parameters) :
    ∀ᵐ x ∂(law P).map leftEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → x i < u →
      rho (P.κ i) (P.m i) w / 10 ≤
        (condDistrib rightEndpoint leftEndpoint (law P) x).real
          {y : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [right_condDistrib_crossing_lower P] with x hx i w u hw hu0 hu1 hxu
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hx i w u hw hu0 hu1 hxu)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal (rho_nonneg (P.κ_nonneg i)),
    ENNReal.toReal_ofNat, measureReal_def] using h

theorem left_condDistrib_crossing_real_lower (P : Parameters) :
    ∀ᵐ y ∂(law P).map rightEndpoint, ∀ (i : ℕ) (w u : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u → u ≤ 1 - w → u ≤ y i →
      rho (P.κ i) (P.m i) w / 10 ≤
        (condDistrib leftEndpoint rightEndpoint (law P) y).real
          {x : Endpoint | x i < u ∧ u ≤ y i} := by
  filter_upwards [left_condDistrib_crossing_lower P] with y hy i w u hw hu0 hu1 huy
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (hy i w u hw hu0 hu1 huy)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal (rho_nonneg (P.κ_nonneg i)),
    ENNReal.toReal_ofNat, measureReal_def] using h

end Invariant233.OrderedProductCoupling

end

end OAI
