import OAI.Geometry.RCD.Sobolev.LeftQuotientDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Rademacher

namespace OAI

/-! # Integrating a Lipschitz curve's prescribed left derivative -/

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace RegularPointCoordinates

theorem integral_eq_sub_of_lipschitz_left_derivative {F q : ℝ → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {a b : ℝ} (hab : a ≤ b)
    (hq : ∀ x ∈ Ioo a b, HasDerivWithinAt F (q x) (Iio x) x) :
    IntervalIntegrable q volume a b ∧ (∫ x in a..b, q x) = F b-F a := by
  have hAC : AbsolutelyContinuousOnInterval F a b :=
    hF.lipschitzOnWith.absolutelyContinuousOnInterval
  have heq : q =ᵐ[volume.restrict (Ioo a b)] deriv F := by
    filter_upwards [ae_restrict_of_ae hF.ae_differentiableAt,
      ae_restrict_mem measurableSet_Ioo] with x hx hxab
    have hn : x ∉ Iio x := by simp
    have hleft := (hasDerivWithinAt_iff_tendsto_slope' hn).mp (hq x hxab)
    have hdiff := (hasDerivWithinAt_iff_tendsto_slope' hn).mp hx.hasDerivAt.hasDerivWithinAt
    exact tendsto_nhds_unique hleft hdiff
  have heqcc : q =ᵐ[volume.restrict (Icc a b)] deriv F := by
    rwa [←restrict_Ioo_eq_restrict_Icc]
  have heqoc : q =ᵐ[volume.restrict (Ioc a b)] deriv F :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self heqcc
  have hi : IntervalIntegrable q volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hAC.intervalIntegrable_deriv).congr
    exact heqoc.symm
  refine ⟨hi,?_⟩
  rw [intervalIntegral.integral_of_le hab,integral_congr_ae heqoc,
    ←intervalIntegral.integral_of_le hab]
  exact hAC.integral_deriv_eq_sub

end RegularPointCoordinates

end OAI
