import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoerciveMetric
import OAI.Geometry.WeakMTW.Variations.MajorantHessian
import OAI.Geometry.WeakMTW.Potentials.SmoothEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace QuadraticEnvelope
 theorem norm_eventually_difference_lt {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
     {f : X → V} {x : X} (hf : ContinuousAt f x) {r : ℝ} (hr : 0 < r) :
     ∀ᶠ y in 𝓝 x, ‖f y-f x‖ < r := by
   have hc := (hf.sub (continuousAt_const (y := f x))).norm
   exact hc.preimage_mem_nhds (Iio_mem_nhds (by simpa only [Pi.sub_apply,sub_self,norm_zero] using hr))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
 local instance realNormedE : NormedSpace ℝ E := inferInstance

omit [FiniteDimensional ℝ E] in
 theorem slice_hessian {g : E×F → ℝ} {x : E} {p : F}
     (hg : ContDiffAt ℝ 2 g (x,p)) (v : E) :
     fderiv ℝ (fderiv ℝ (fun X => g (X,p))) x v v =
       fderiv ℝ (fderiv ℝ g) (x,p) (v,0) (v,0) := by
   let L : E →L[ℝ] E×F := (ContinuousLinearMap.id ℝ E).prod 0
   have hg' : ContDiffAt ℝ 2 g ((0,p)+L x) := by simpa [L] using hg
   have hh := DiscreteVariational.hessian_affine_pullback L ((0,p) : E×F) hg' v
   simpa only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
     zero_apply,Prod.mk_add_mk,zero_add,add_zero] using hh

 theorem family_positive_bounds {A : Type*} [TopologicalSpace A]
     {k : A → E → ℝ} {P : A → F} {g : E×F → ℝ} {a : A} {Z : E}
     (hP : ContinuousAt P a) (hg : ContDiffAt ℝ ∞ g (Z,P a))
     (heq : ∀ᶠ a' in 𝓝 a, ∀ X, k a' X = g (X,P a'))
     (hpos : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (k a)) Z v v) :
     ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧
       ∀ a' ∈ U, ∀ X ∈ Metric.ball Z r,
         ContDiffAt ℝ 2 (k a') X ∧ ∀ v : E, κ*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ (k a')) X v v := by
   obtain ⟨m,hm,hco⟩ := CoordinateGeometry.positive_metric_coercive hpos
   have heqa : k a = fun X => g (X,P a) := funext (mem_of_mem_nhds heq)
   have hco' (v : E) : m*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ g) (Z,P a) (v,0) (v,0) := by
     have h := hco v
     rw [heqa,slice_hessian (hg.of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) v] at h
     exact h
   have hs : ∀ᶠ W in 𝓝 (Z,P a), ContDiffAt ℝ 2 g W :=
     (hg.of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
   have hH := hessian_continuous hg
   have hh : ∀ᶠ W in 𝓝 (Z,P a),
       ‖fderiv ℝ (fderiv ℝ g) W-fderiv ℝ (fderiv ℝ g) (Z,P a)‖ < m/2 :=
     norm_eventually_difference_lt (f := fderiv ℝ (fderiv ℝ g)) hH (half_pos hm)
   obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp (hs.and hh)
   have hp : ∀ᶠ a' in 𝓝 a, dist (P a') (P a) < r := hP.tendsto (Metric.ball_mem_nhds _ hr)
   obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp (hp.and heq)
   refine ⟨U,hU,haU,r,m/2,hr,half_pos hm,?_⟩
   intro a' ha' X hX
   have hW : (X,P a') ∈ Metric.ball (Z,P a) r := by
     rw [Metric.mem_ball,Prod.dist_eq]
     exact max_lt hX (hUsub ha').1
   have hk : k a' = fun Y => g (Y,P a') := funext (hUsub ha').2
   rw [hk]
   refine ⟨(hrb hW).1.comp X (contDiffAt_id.prodMk contDiffAt_const),fun v => ?_⟩
   rw [slice_hessian (hrb hW).1 v]
   have hn := ContinuousLinearMap.le_opNorm₂
     (fderiv ℝ (fderiv ℝ g) (X,P a')-fderiv ℝ (fderiv ℝ g) (Z,P a)) (v,0) (v,0)
   simp only [sub_apply,Real.norm_eq_abs,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg v)] at hn
   have hdiff : ‖fderiv ℝ (fderiv ℝ g) (X,P a')-fderiv ℝ (fderiv ℝ g) (Z,P a)‖ ≤ m/2 :=
     (hrb hW).2.le
   have hb := mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖v‖)
   have hi := hco' v
   have ho := (abs_le.mp hn).1
   nlinarith

omit [FiniteDimensional ℝ E] in
 theorem positive_hessian_growth {g : E → ℝ} {c : E} {r κ : ℝ}
     (h : ∀ X ∈ Metric.ball c r, ContDiffAt ℝ 2 g X ∧
       ∀ v : E, κ*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ g) X v v)
     {x y : E} (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r)
     (hc : fderiv ℝ g x = 0) : κ/2*‖y-x‖^2 ≤ g y-g x := by
   have hseg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : x+t•(y-x) ∈ Metric.ball c r := by
     have he : x+t•(y-x) = (1-t)•x+t•y := by module
     rw [he]
     exact (convex_ball c r) hx hy (by linarith [ht.2]) ht.1 (by ring)
   obtain ⟨t,ht,he⟩ := MovingTaylor.second_segment x (y-x) (fun t ht => (h _ (hseg t ht)).1)
   rw [add_sub_cancel,hc,zero_apply,sub_zero] at he
   have hb := (h _ (hseg t ⟨ht.1.le,ht.2.le⟩)).2 (y-x)
   linarith
end QuadraticEnvelope
end

end WeakMTWGlobalSupport

end OAI
