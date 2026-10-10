import Mathlib
import OAI.Geometry.WeakMTW.Variations.DiscreteVariationalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem hessian_majorant {f : E → ℝ} {g : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (L x))
    (heq : f x = g (L x)) (hle : ∀ᶠ z in 𝓝 x, g (L z) ≤ f z) (v : E) :
    fderiv ℝ (fderiv ℝ g) (L x) (L v) (L v) ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let a : ℝ → ℝ := fun t => f (x+t•v)
  let b : ℝ → ℝ := fun t => g (L x+t•L v)
  have hline : ContDiff ℝ 2 (fun t : ℝ => x+t•v) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline' : ContDiff ℝ 2 (fun t : ℝ => L x+t•L v) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have ha : ContDiffAt ℝ 2 a 0 := by
    have hf' : ContDiffAt ℝ 2 f (x+(0 : ℝ)•v) := by simpa using hf
    exact hf'.comp 0 hline.contDiffAt
  have hb : ContDiffAt ℝ 2 b 0 := by
    have hg' : ContDiffAt ℝ 2 g (L x+(0 : ℝ)•L v) := by simpa using hg
    exact hg'.comp 0 hline'.contDiffAt
  have hm : IsLocalMin (a-b) 0 := by
    have ht : Tendsto (fun t : ℝ => x+t•v) (𝓝 0) (𝓝 x) := by
      simpa using hline.continuous.continuousAt.tendsto (x := (0 : ℝ))
    filter_upwards [ht hle] with t htt
    change f (x+(0 : ℝ)•v)-g (L x+(0 : ℝ)•L v) ≤ f (x+t•v)-g (L x+t•L v)
    simp only [zero_smul,add_zero,heq,sub_self]
    apply sub_nonneg.mpr
    change g (L (x+t•v)) ≤ f (x+t•v) at htt
    simpa only [map_add,map_smul] using htt
  have hh := scalar_second_nonneg hm (ha.sub hb).continuousAt
  have hsub := iteratedDeriv_sub (n := 2) ha hb
  have hs : deriv (deriv (a-b)) 0 = deriv (deriv a) 0-deriv (deriv b) 0 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def] using hsub
  rw [hs] at hh
  have hfa := line_second hf v
  have hgb := line_second hg (L v)
  change deriv (deriv a) 0 = _ at hfa
  change deriv (deriv b) 0 = _ at hgb
  rw [hfa,hgb] at hh
  linarith

 theorem hessian_affine_pullback (L : E →L[ℝ] F) (c : F) {f : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (c+L x)) (v : E) :
    fderiv ℝ (fderiv ℝ (fun u => f (c+L u))) x v v =
      fderiv ℝ (fderiv ℝ f) (c+L x) (L v) (L v) := by
  have hcomp : ContDiffAt ℝ 2 (fun u => f (c+L u)) x :=
    hf.comp x (contDiffAt_const.add L.contDiff.contDiffAt)
  rw [← line_second hcomp v,← line_second hf (L v)]
  congr 2
  funext t
  simp only [map_add,map_smul,add_assoc]

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
