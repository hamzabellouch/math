import Mathlib
import OAI.Geometry.WeakMTW.Variations.MajorantHessian
import OAI.Geometry.WeakMTW.Variations.LineTaylor
import OAI.Geometry.WeakMTW.Potentials.QuadraticEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuadraticEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 def DiagonalBound (g : E → ℝ) (X : E) (K : ℝ) : Prop :=
   ContDiffAt ℝ 2 g X ∧ ∀ v : E, |fderiv ℝ (fderiv ℝ g) X v v| ≤ K*‖v‖^2

 theorem DiagonalBound.mono {g : E → ℝ} {X : E} {K L : ℝ}
     (h : DiagonalBound g X K) (hKL : K ≤ L) : DiagonalBound g X L :=
   ⟨h.1,fun v => (h.2 v).trans (mul_le_mul_of_nonneg_right hKL (sq_nonneg _))⟩

 theorem slice_diagonal_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
     {g : E×F → ℝ} {x : E} {p : F} {K : ℝ}
     (hg : ContDiffAt ℝ 2 g (x,p)) (hB : ‖fderiv ℝ (fderiv ℝ g) (x,p)‖ ≤ K) :
     DiagonalBound (fun X : E => g (X,p)) x K := by
   let L : E →L[ℝ] E×F := (ContinuousLinearMap.id ℝ E).prod 0
   have hp : ContDiffAt ℝ 2 (fun X : E => (X,p)) x := contDiffAt_id.prodMk contDiffAt_const
   refine ⟨hg.comp x hp,fun v => ?_⟩
   have hg' : ContDiffAt ℝ 2 g ((0,p)+L x) := by simpa [L] using hg
   have hessian := DiscreteVariational.hessian_affine_pullback L ((0,p) : E×F) hg' v
   simp only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
     zero_apply,Prod.mk_add_mk,zero_add,add_zero] at hessian
   rw [hessian]
   have hn := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ g) (x,p)) (v,0) (v,0)
   simp only [Real.norm_eq_abs,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg v)] at hn
   have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖v‖)
   nlinarith

 theorem diagonal_quadratic_bound {g : E → ℝ} {c : E} {r K : ℝ}
     (hK : 0 ≤ K) (h : ∀ X ∈ Metric.ball c r, DiagonalBound g X K)
     {x y : E} (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) :
     |g y-g x-fderiv ℝ g x (y-x)| ≤ K*‖y-x‖^2 := by
   have hseg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : x+t•(y-x) ∈ Metric.ball c r := by
     have he : x+t•(y-x) = (1-t)•x+t•y := by module
     rw [he]
     exact (convex_ball c r) hx hy (by linarith [ht.2]) ht.1 (by ring)
   obtain ⟨t,ht,he⟩ := MovingTaylor.second_segment x (y-x) (fun t ht => (h _ (hseg t ht)).1)
   rw [add_sub_cancel] at he
   rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
   have hb := (h _ (hseg t ⟨ht.1.le,ht.2.le⟩)).2 (y-x)
   nlinarith [mul_nonneg hK (sq_nonneg ‖y-x‖)]

 theorem support_differentials_equal {f g h : E → ℝ} {x : E}
     (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
     (hs : ∀ y : E, f x+h y-h x ≤ f y ∧ f y ≤ f x+g y-g x) :
     fderiv ℝ g x = fderiv ℝ h x := by
   have hmin : IsLocalMin (fun y => g y-h y) x := by
     apply Filter.Eventually.of_forall
     intro y
     change g x-h x ≤ g y-h y
     linarith [(hs y).1,(hs y).2]
   exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hh.hasFDerivAt))

 theorem two_sided_uniform {f : E → ℝ} {g h : E → E → ℝ} {c : E} {r K : ℝ}
     (hr : 0 < r) (hK : 0 ≤ K)
     (hb : ∀ x ∈ Metric.ball c r, ∀ X ∈ Metric.ball c r,
       DiagonalBound (g x) X K ∧ DiagonalBound (h x) X K)
     (hs : ∀ x ∈ Metric.ball c r, ∀ y : E,
       f x+h x y-h x x ≤ f y ∧ f y ≤ f x+g x y-g x x) :
     ContDiffAt ℝ 1 f c ∧ LipschitzOnWith ⟨12*K,by positivity⟩ (fderiv ℝ f) (Metric.ball c (r/4)) := by
   let D (x : E) := fderiv ℝ (g x) x
   have hd (x : E) (hx : x ∈ Metric.ball c r) : D x = fderiv ℝ (h x) x :=
     support_differentials_equal ((hb x hx x hx).1.1.differentiableAt (by norm_num))
       ((hb x hx x hx).2.1.differentiableAt (by norm_num)) (hs x hx)
   have hquad (x : E) (hx : x ∈ Metric.ball c r) (y : E) (hy : y ∈ Metric.ball c r) :
       |f y-f x-D x (y-x)| ≤ (2*K)*‖y-x‖^2 := by
     have hg := diagonal_quadratic_bound hK (fun X hX => (hb x hx X hX).1) hx hy
     have hh := diagonal_quadratic_bound hK (fun X hX => (hb x hx X hX).2) hx hy
     change |g x y-g x x-D x (y-x)| ≤ _ at hg
     rw [←hd x hx] at hh
     rw [abs_le] at hg hh ⊢
     constructor <;> nlinarith [(hs x hx y).1,(hs x hx y).2,mul_nonneg hK (sq_nonneg ‖y-x‖)]
   have hD (x : E) (hx : x ∈ Metric.ball c r) : HasFDerivAt f (D x) x :=
     hasFDerivAt_of_bound (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) (hquad x hx))
   refine ⟨(c1_of_bound hr (by positivity) hquad).1,?_⟩
   have hLip := differential_lipschitz hr (by positivity) hquad
   apply LipschitzOnWith.of_dist_le_mul
   intro x hx y hy
   have hsub : Metric.ball c (r/4) ⊆ Metric.ball c r := Metric.ball_subset_ball (by linarith)
   rw [(hD x (hsub hx)).fderiv,(hD y (hsub hy)).fderiv]
   have hh := hLip.dist_le_mul x hx y hy
   convert hh using 1
   ring_nf
end QuadraticEnvelope
end

end WeakMTWGlobalSupport

end OAI
