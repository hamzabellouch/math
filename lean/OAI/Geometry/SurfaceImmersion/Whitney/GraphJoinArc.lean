import OAI.Geometry.SurfaceImmersion.Geometry.RoundedReturnRegular
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Smooth graph interpolation rounds corners whose two oriented branches
both advance in the same coordinate direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def graphJoinCurve (f g : ℝ → ℝ) (t : ℝ) : Base :=
  ![t,(1-centeredSmoothStep t)*f t+centeredSmoothStep t*g t]

lemma graphJoinCurve_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (graphJoinCurve f g) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact ((contDiff_const.sub centeredSmoothStep_smooth).mul hf).add
      (centeredSmoothStep_smooth.mul hg)

lemma graphJoinCurve_injective (f g : ℝ → ℝ) : Function.Injective (graphJoinCurve f g) := by
  intro x y h
  exact congrFun h 0

lemma graphJoinCurve_regular {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (graphJoinCurve f g) t) := by
  have hC := (graphJoinCurve_smooth hf hg).differentiable (by simp) t
  have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
  have hd : deriv (graphJoinCurve f g) t 0 = 1 := hc0.unique (hasDerivAt_id t)
  apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
  rw [hd]
  norm_num

theorem graph_join_arc {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = graphJoinCurve f g ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![t,f t]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![t,g t]) := by
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨graphJoinCurve f g,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (graphJoinCurve_smooth hf hg).contMDiff.contMDiffOn,
      fun t _ => graphJoinCurve_regular hf hg t,(graphJoinCurve_injective f g).injOn⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    simp [P,graphJoinCurve,centeredSmoothStep_zero ht.le]
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    simp [P,graphJoinCurve,centeredSmoothStep_one ht.le]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
