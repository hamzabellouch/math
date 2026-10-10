import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Calculus
import OAI.Analysis.BiholderTransport.Regularity.StationaryPullback
import OAI.Analysis.BiholderTransport.LinearAlgebra.LocalMountains

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma convexOn_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S,ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S,∀ d:E,0≤fderiv ℝ (fderiv ℝ f) z d d) : ConvexOn ℝ S f := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  exact ⟨fderiv ℝ f x,fun y hy => lower_support_of_nonnegative_hessian hS hf hH hx hy⟩

lemma strongConvexOn_of_hessian_lower {f : E → ℝ} {S : Set E} {m : ℝ}
    (hS : Convex ℝ S) (hf : ∀ z∈S,ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S,∀ d:E,m*‖d‖^2≤fderiv ℝ (fderiv ℝ f) z d d) :
    StrongConvexOn S m f := by
  rw [strongConvexOn_iff_convex]
  have hN (z:E) : ContDiffAt ℝ 2 (fun w:E => ‖w‖^2/2) z :=
    (half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have he : (fun z => f z-m/2*‖z‖^2)=(fun z => f z-m*(‖z‖^2/2)) := by
    ext z; ring
  rw [he]
  apply convexOn_of_nonnegative_hessian hS
    (fun z hz => (hf z hz).sub (contDiffAt_const.mul (hN z)))
  intro z hz d
  rw [second_fderiv_sub (hf z hz) (contDiffAt_const.mul (hN z)),
    second_fderiv_const_mul,half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (hH z hz d)

lemma StrongConvexOn.quadratic_growth_half {f : E → ℝ} {S : Set E} {m : ℝ}
    (hf : StrongConvexOn S m f) {x y:E} (hx:x∈S) (hy:y∈S)
    (hmin : IsMinOn f S x) : f x+(m/4)*‖y-x‖^2≤f y := by
  have H := hf.2 hx hy (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  have HM := hmin (hf.1 hx hy (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1))
  change f ((1/2:ℝ) • x+(1/2:ℝ) • y)≤
    (1/2:ℝ)*f x+(1/2:ℝ)*f y-(1/2:ℝ)*(1/2:ℝ)*(m/2*‖x-y‖^2) at H
  rw [norm_sub_rev] at H
  change f x≤f ((1/2:ℝ) • x+(1/2:ℝ) • y) at HM
  linarith only [H,HM]

lemma strongConvexOn_add_semiconvex {f g : E → ℝ} {S : Set E} {m K t : ℝ}
    (hf : StrongConvexOn S m f) (hg : ConvexOn ℝ S (fun x => g x+K/2*‖x‖^2))
    (ht : 0≤t) : StrongConvexOn S (m-t*K) (fun x => f x+t*g x) := by
  rw [strongConvexOn_iff_convex] at hf ⊢
  have HF : ConvexOn ℝ S (fun x => (f x-m/2*‖x‖^2)+t*(g x+K/2*‖x‖^2)) :=
    hf.add (hg.smul ht)
  convert HF using 1
  ext x
  ring

end WeakMTWTransport
end

end OAI
