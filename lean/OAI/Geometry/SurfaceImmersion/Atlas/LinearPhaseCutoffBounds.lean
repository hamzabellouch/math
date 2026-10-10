import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseDerivativeBounds
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedChartTransport
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! Quantitative transport of the actual supported cutoff to a linear
phase chart, including the inverse frequency factor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseGeometry RealModes

def phaseCutoffBudget (m : ℕ) (C J W : ℝ) : ℝ := W*((m.factorial : ℝ)*C*J^m)

lemma phaseCutoffBudget_polynomial (m : ℕ) {C J W : ℝ → ℝ}
    (hC : HasPolynomialBound C) (hJ : HasPolynomialBound J) (hW : HasPolynomialBound W) :
    HasPolynomialBound (fun x => phaseCutoffBudget m (C x) (J x) (W x)) :=
  hW.mul (((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul hC).mul (hJ.pow m))

theorem linear_phase_cutoff_bound {U : Set SmallModes.Base} (hU : IsOpen U)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ U) {s : ℝ≥0} {C J W w : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hJ : 1 ≤ J)
    (hi : ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ J) (hw : |w⁻¹| ≤ W)
    (f : SupportedField (F := ℝ) K) (hf : WeightedBound univ s m C f) :
    WeightedBound univ s m (phaseCutoffBudget m C J W)
      (w⁻¹ • chartPush (linearPhaseChart ξ hξ U hU)
        (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK f) := by
  let e := linearPhaseChart ξ hξ U hU
  let g := chartPush e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK f
  have hj (j : ℕ) (hj : 1 ≤ j) (_hjm : j ≤ m) (y : SmallModes.Base) (hy : y ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J :=
    (positive_order_linear_derivative_le (phaseEquiv ξ hξ).symm.toContinuousLinearMap
      e.open_target hj hy).trans hi
  have hseminorm := chartPush_bound e
    (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn K hK hs hs1 hJ hj f
  have hpush : WeightedBound univ s m ((m.factorial : ℝ)*C*J^m) g := by
    apply (weightedBound_of_supportedSeminorm s m g).mono_const
    exact hseminorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (supportedSeminorm_le_of_weightedBound hs hC f hf)
        (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hJ) _))
  have hscale := hpush.const_smul uniqueDiffOn_univ g.contDiff.contDiffOn (w⁻¹)
  apply hscale.mono_const
  exact mul_le_mul_of_nonneg_right hw
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (pow_nonneg (zero_le_one.trans hJ) _))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
