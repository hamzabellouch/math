import OAI.Geometry.SurfaceImmersion.Geometry.RoundedReturnCurve

namespace OAI

/-! The explicit graph U-turn has nonzero velocity even at its turning
point; away from it, the first coordinate already has nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma plane_curve_regular_of_hasDerivAt {C : ℝ → Base} {v : Base} {t : ℝ}
    (hC : HasDerivAt C v t) {i : Fin 2} (hi : v i ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) C t) := by
  have hD := hC.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hD]
  intro x y hxy
  change ℝ at x y
  have h := congrFun hxy i
  change x*v i = y*v i at h
  exact (mul_right_cancel₀ hi h : (x : ℝ) = (y : ℝ))

lemma roundedReturnCurve_hasDerivAt_zero {f g : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a) :
    HasDerivAt (roundedReturnCurve f g a b) (![0,g a-f a] : Base) 0 := by
  have hx : HasDerivAt (fun t : ℝ => a+b*t^2) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).const_mul b).const_add a using 1 <;> norm_num
  have hF : HasDerivAt (fun t : ℝ => f (a+b*t^2)) 0 0 := by
    have hf' : HasDerivAt f (deriv f a) (a+b*(0:ℝ)^2) := by simpa using hf.hasDerivAt
    simpa only [mul_zero,Function.comp_def] using hf'.comp 0 hx
  have hG : HasDerivAt (fun t : ℝ => g (a+b*t^2)) 0 0 := by
    have hg' : HasDerivAt g (deriv g a) (a+b*(0:ℝ)^2) := by simpa using hg.hasDerivAt
    simpa only [mul_zero,Function.comp_def] using hg'.comp 0 hx
  have hy : HasDerivAt (fun t : ℝ =>
      (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2)) (g a-f a) 0 := by
    convert ((centeredSmoothStep_hasDerivAt_zero.const_sub 1).mul hF).add
      (centeredSmoothStep_hasDerivAt_zero.mul hG) using 1
    all_goals first | rfl | (norm_num; ring)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hx
  · exact hy

theorem roundedReturnCurve_regular {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hb : 0 < b) (hgap : f a < g a) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (roundedReturnCurve f g a b) t) := by
  by_cases ht : t = 0
  · subst t
    apply plane_curve_regular_of_hasDerivAt
      (roundedReturnCurve_hasDerivAt_zero (hf.differentiable (by simp) a) (hg.differentiable (by simp) a))
      (i := 1)
    exact sub_ne_zero.mpr (ne_of_gt hgap)
  · have hx : HasDerivAt (fun u : ℝ => a+b*u^2) (2*b*t) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul b).const_add a using 1
      · rfl
      · dsimp only [id_eq]
        ring
    have hC := (roundedReturnCurve_smooth hf hg a b).differentiable (by simp) t
    have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
    have hcoord : deriv (roundedReturnCurve f g a b) t 0 = 2*b*t := hc0.unique hx
    apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
    rw [hcoord]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb.ne') ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
