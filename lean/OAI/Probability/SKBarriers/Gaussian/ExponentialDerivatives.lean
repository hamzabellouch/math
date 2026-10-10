import Mathlib
import OAI.Probability.SKBarriers.Gaussian.ExponentialGrowth

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section ExponentialDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_exp_growth (f : E → ℝ) (hf : Differentiable ℝ f)
    (hg : HasExpGrowth (fun x => Real.exp (f x)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    HasExpGrowth (fderiv ℝ (fun x => Real.exp (f x))) := by
  apply hg.congr_bound hC
  intro x
  rw [fderiv_exp (hf x), norm_smul]
  exact (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem fderiv_fderiv_exp (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => Real.exp (f z))) x =
      Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x +
      (Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x) := by
  have hd := hf.differentiable (by norm_num)
  have hh : fderiv ℝ (fun z => Real.exp (f z)) = fun z => Real.exp (f z) • fderiv ℝ f z := by
    funext z
    exact fderiv_exp (hd z)
  rw [hh]
  exact ((hd x).hasFDerivAt.exp.smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem fderiv_fderiv_exp_growth (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth (fun x => Real.exp (f x)))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D) :
    HasExpGrowth (fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x)))) := by
  apply hg.congr_bound (show 0 ≤ D+C*C by positivity)
  intro x
  rw [fderiv_fderiv_exp f hf x]
  calc
    _ ≤ ‖Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖Real.exp (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖+
        (‖Real.exp (f x)‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖Real.exp (f x)‖*D+(‖Real.exp (f x)‖*C)*C := by gcongr <;> first | exact hb _ | exact hbb _
    _ = _ := by ring

end ExponentialDerivatives
end SK.Analytic

end
end
end
end
end
end

end OAI
