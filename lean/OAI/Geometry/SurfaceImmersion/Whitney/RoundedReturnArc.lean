import OAI.Geometry.SurfaceImmersion.Geometry.RoundedReturnRegular
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! A compact smooth embedded rounding of a returning pair of graph arcs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem rounded_return_arc {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {a b : ℝ} (hb : 0 < b) (hgap : ∀ x ∈ Icc a (a+4*b), f x < g x) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = roundedReturnCurve f g a b ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![a+b*t^2,f (a+b*t^2)]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![a+b*t^2,g (a+b*t^2)]) ∧
      P.curve P.start = ![a+4*b,f (a+4*b)] ∧
      P.curve P.finish = ![a+4*b,g (a+4*b)] := by
  have hgapa : f a < g a := hgap a ⟨le_rfl,by linarith⟩
  have hgap' : ∀ x ∈ Icc a (a+b*(2:ℝ)^2), f x < g x := by
    have he : a+b*(2:ℝ)^2 = a+4*b := by ring
    rw [he]
    exact hgap
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨roundedReturnCurve f g a b,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (roundedReturnCurve_smooth hf hg a b).contMDiff.contMDiffOn,
      fun t _ => roundedReturnCurve_regular hf hg hb hgapa t,
      roundedReturnCurve_injective hb hgap'⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    exact roundedReturnCurve_left ht.le
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    exact roundedReturnCurve_right ht.le
  · change roundedReturnCurve f g a b (-2) = _
    rw [roundedReturnCurve_left (by norm_num)]
    have he : a+b*(-2:ℝ)^2 = a+4*b := by ring
    rw [he]
  · change roundedReturnCurve f g a b 2 = _
    rw [roundedReturnCurve_right (by norm_num)]
    have he : a+b*(2:ℝ)^2 = a+4*b := by ring
    rw [he]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
