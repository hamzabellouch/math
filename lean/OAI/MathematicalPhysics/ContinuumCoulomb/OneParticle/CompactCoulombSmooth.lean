import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.DensitySynthesis
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! Smooth Coulomb fields of compact source pieces. Derivatives are moved
to the density, which avoids differentiating through the Coulomb pole. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem potentialOf_eq_convolution (q : Position → ℝ) :
    NeutralAtom.potentialOf q =
      NeutralAtom.coulombKernel ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] q := by
  funext y
  change (∫ x, NeutralAtom.coulombKernel (y-x)*q x) =
    ∫ x, NeutralAtom.coulombKernel x*q (y-x)
  rw [← integral_sub_left_eq_self (fun x => NeutralAtom.coulombKernel (y-x)*q x) volume y]
  simp only [sub_sub_cancel]

theorem compact_coulomb_C4 {q : Position → ℝ} (hq : ContDiff ℝ 4 q)
    (hc : HasCompactSupport q) : ContDiff ℝ 4 (NeutralAtom.potentialOf q) := by
  rw [potentialOf_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq

theorem compact_coulomb_partial {q : Position → ℝ} (hq : ContDiff ℝ 1 q)
    (hc : HasCompactSupport q) (v y : Position) :
    NeutralAtom.dirPartial (NeutralAtom.potentialOf q) v y =
      NeutralAtom.potentialOf (NeutralAtom.dirPartial q v) y := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    NeutralAtom.locallyIntegrable_coulombKernel hq y
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR Position)
    NeutralAtom.locallyIntegrable_coulombKernel (hq.continuous_fderiv (by norm_num)) y
  change fderiv ℝ (NeutralAtom.potentialOf q) y v = _
  rw [potentialOf_eq_convolution,hd.fderiv]
  change (∫ x, (ContinuousLinearMap.mul ℝ ℝ).precompR Position
    (NeutralAtom.coulombKernel x) (fderiv ℝ q (y-x))) v = _
  rw [ContinuousLinearMap.integral_apply hi v,potentialOf_eq_convolution]
  rfl

theorem compact_coulomb_bound {q : Position → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) {M : ℝ} (hM : ∀ x, ‖q x‖ ≤ M) (y : Position) :
    ‖NeutralAtom.potentialOf q y‖ ≤ 2*Real.pi*M+∫ x, ‖q x‖ := by
  have he := Coulomb.coulomb_convolution_bound (hq.integrable_of_hasCompactSupport hc).norm
    hq.measurable.norm (fun x => norm_nonneg (q x)) hM (by norm_num : (0:ℝ) < 1) y
  have hn := norm_integral_le_integral_norm (μ := volume)
    (fun x => NeutralAtom.coulombKernel (y-x)*q x)
  simp only [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _)] at hn
  apply hn.trans
  simpa only [one_pow,mul_one,inv_one,one_mul,Coulomb.coulombKernel,NeutralAtom.coulombKernel] using he

end ContinuumCoulomb

end

end OAI
