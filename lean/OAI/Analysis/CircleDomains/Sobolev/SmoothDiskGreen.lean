import OAI.Analysis.CircleDomains.Topology.RoundDiskGreen
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI

/-! The two concrete Green identities used for the conductivity map:
its smooth Jacobian is an actual boundary integral, and its vertical
partial derivative is the corresponding outward flux. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_complex_partial_commute {v : ℂ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (z p q : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w q) z p =
      fderiv ℝ (fun w => fderiv ℝ v w p) z q := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    ((hv.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.contDiffAt.isSymmSndFDerivAt (by simp) _ _

 theorem smooth_disk_vertical_flux (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {v : ℂ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ z in ball (0 : ℂ) R, fderiv ℝ v z Complex.I) =
      planarFormIntegral (fun z => -v z) (fun _ => 0) (unitCircleParam 0 R) := by
  rw [round_disk_green hgreen R hR univ isOpen_univ (subset_univ _)
    _ _ hv.neg.contDiffOn contDiff_const.contDiffOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp only [fderiv_const_apply, fderiv_fun_neg, zero_apply, neg_apply, zero_sub, neg_neg]

 theorem smooth_disk_jacobian (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a b : ℂ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    (∫ z in ball (0 : ℂ) R,
      fderiv ℝ a z 1 * fderiv ℝ b z Complex.I -
        fderiv ℝ a z Complex.I * fderiv ℝ b z 1) =
      planarFormIntegral (fun z => a z * fderiv ℝ b z 1)
        (fun z => a z * fderiv ℝ b z Complex.I) (unitCircleParam 0 R) := by
  have hb' (p : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ b z p) :=
    (hb.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  rw [round_disk_green hgreen R hR univ isOpen_univ (subset_univ _)
    _ _ (ha.mul (hb' 1)).contDiffOn (ha.mul (hb' Complex.I)).contDiffOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [fderiv_fun_mul (ha.differentiable (by simp)).differentiableAt
      ((hb' Complex.I).differentiable (by simp)).differentiableAt,
    fderiv_fun_mul (ha.differentiable (by simp)).differentiableAt
      ((hb' 1).differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [smooth_complex_partial_commute hb z 1 Complex.I]
  ring

end CircleDomainRigidity

end

end OAI
