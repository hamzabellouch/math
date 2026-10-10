import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.PowerDual

namespace OAI

/-! Power Integration. -/

section

 
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def dir (v : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_smooth (v : E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dir_compact (v : E) {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (dir v f) :=
  (hf.fderiv ℝ).comp_left (g:=fun L : E →L[ℝ] ℝ => L v) (by simp : (fun L : E →L[ℝ] ℝ => L v) 0 = 0)

lemma power_dir_integration {p : ℝ} (hp : 2 < p) (v : E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, |dir v f x|^p) = -(p-1) *
      ∫ x, f x * |dir v f x|^(p-2) * dir v (dir v f) x := by
  let a := dir v f
  let b := dir v a
  have ha : ContDiff ℝ ∞ a := dir_smooth v hf
  have hb : ContDiff ℝ ∞ b := dir_smooth v ha
  have hac : HasCompactSupport a := dir_compact v hc
  have hbc : HasCompactSupport b := dir_compact v hac
  have hpow : Continuous (fun x => |a x|^(p-2)) := ha.continuous.abs.rpow_const (fun _ => Or.inr (by linarith))
  have hdual : Continuous (fun x => powerDual p (a x)) := (powerDual_continuous hp).comp ha.continuous
  have hdval (x : E) : fderiv ℝ (fun x => powerDual p (a x)) x v = (p-1)*|a x|^(p-2)*b x := by
    have h := (powerDual_hasDerivAt hp (a x)).hasFDerivAt.comp x (ha.differentiable (by simp) x).hasFDerivAt
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
    dsimp only [Function.comp_def] at he
    rw [he]
    simp only [ContinuousLinearMap.comp_apply]
    change (fderiv ℝ a x v) * ((p-1)*|a x|^(p-2)) = _
    exact mul_comm _ _
  have h1 : Integrable (fun x => fderiv ℝ f x v * powerDual p (a x)) :=
    (ha.continuous.mul hdual).integrable_of_hasCompactSupport hac.mul_right
  have h2 : Integrable (fun x => f x * fderiv ℝ (fun x => powerDual p (a x)) x v) := by
    simp_rw [hdval]
    exact (hf.continuous.mul ((continuous_const.mul hpow).mul hb.continuous)).integrable_of_hasCompactSupport hc.mul_right
  have h3 : Integrable (fun x => f x * powerDual p (a x)) :=
    (hf.continuous.mul hdual).integrable_of_hasCompactSupport hc.mul_right
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => ((powerDual_hasDerivAt hp (a x)).differentiableAt.comp x (ha.differentiable (by simp) x)))
  have hright : (fun x => fderiv ℝ f x v * powerDual p (a x)) = (fun x => |a x|^p) := by
    funext x
    exact (mul_comm _ _).trans (powerDual_mul_self hp (a x))
  have hleft : (fun x => f x * fderiv ℝ (fun x => powerDual p (a x)) x v) =
      (fun x => (p-1)*(f x*|a x|^(p-2)*b x)) := by
    funext x
    rw [hdval]
    ring
  rw [hright,hleft,integral_const_mul] at he
  dsimp only [a,b] at he
  linarith
end TameInterpolation

end
end

end OAI
