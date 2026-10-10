import OAI.Geometry.SurfaceImmersion.Whitney.GraphJoinArc
import OAI.Geometry.SurfaceImmersion.Geometry.SmallGraphBlends

namespace OAI

/-! A graph corner can be rounded at an arbitrarily small horizontal scale. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def scaledGraphJoin (f g : ℝ → ℝ) (a b t : ℝ) : Base :=
  ![a+b*t,(1-centeredSmoothStep t)*f (a+b*t)+centeredSmoothStep t*g (a+b*t)]

lemma scaledGraphJoin_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) : ContDiff ℝ ∞ (scaledGraphJoin f g a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t => a+b*t)
    fun_prop
  · change ContDiff ℝ ∞ (fun t => (1-centeredSmoothStep t)*f (a+b*t)+centeredSmoothStep t*g (a+b*t))
    exact ((contDiff_const.sub centeredSmoothStep_smooth).mul (hf.comp (by fun_prop))).add
      (centeredSmoothStep_smooth.mul (hg.comp (by fun_prop)))

lemma scaledGraphJoin_injective (f g : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Function.Injective (scaledGraphJoin f g a b) := by
  intro t u he
  have hx := congrFun he 0
  change a+b*t = a+b*u at hx
  exact mul_left_cancel₀ hb (add_left_cancel hx)

lemma scaledGraphJoin_regular {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) {b : ℝ} (hb : b ≠ 0) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (scaledGraphJoin f g a b) t) := by
  have hC := (scaledGraphJoin_smooth hf hg a b).differentiable (by simp) t
  have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
  have hx : HasDerivAt (fun u : ℝ => a+b*u) b t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
  rw [hc0.unique hx]
  exact hb

lemma scaledGraphJoin_eq_blend (f g : ℝ → ℝ) (a b t : ℝ) :
    scaledGraphJoin f g a b t = (1-centeredSmoothStep t) • graphPoint f (a+b*t) +
      centeredSmoothStep t • graphPoint g (a+b*t) := by
  ext i
  fin_cases i
  · change a+b*t = (1-centeredSmoothStep t)*(a+b*t)+centeredSmoothStep t*(a+b*t)
    ring
  · rfl

theorem scaled_graph_join_arc {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = scaledGraphJoin f g a b ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![a+b*t,f (a+b*t)]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![a+b*t,g (a+b*t)]) := by
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨scaledGraphJoin f g a b,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (scaledGraphJoin_smooth hf hg a b).contMDiff.contMDiffOn,
      fun t _ => scaledGraphJoin_regular hf hg a hb t,
      (scaledGraphJoin_injective f g a hb).injOn⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    simp [P,scaledGraphJoin,centeredSmoothStep_zero ht.le]
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    simp [P,scaledGraphJoin,centeredSmoothStep_one ht.le]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
