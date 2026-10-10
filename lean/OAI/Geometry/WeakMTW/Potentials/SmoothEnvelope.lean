import Mathlib
import OAI.Geometry.WeakMTW.Variations.LineTaylor
import OAI.Geometry.WeakMTW.Potentials.QuadraticEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuadraticEnvelope
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem norm_eventually_bound {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
     {f : X → V} {x : X} (hf : ContinuousAt f x) :
     ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ ‖f x‖+1 := by
   have hb : ∀ᶠ y in 𝓝 x, dist (f y) (f x) < 1 :=
     hf.tendsto (Metric.ball_mem_nhds (f x) (by norm_num : (0:ℝ) < 1))
   exact hb.mono (fun y hy => norm_le_norm_add_const_of_dist_le hy.le)

 theorem hessian_continuous {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
     {g : V → ℝ} {v : V} (hg : ContDiffAt ℝ ∞ g v) :
     ContinuousAt (fderiv ℝ (fderiv ℝ g)) v :=
   ((hg.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt

 theorem smooth_local_bounds {g : E × F → ℝ} {a : E} {b : F}
     (hg : ContDiffAt ℝ ∞ g (a,b)) :
     ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ ∀ q ∈ Metric.ball (a,b) r,
       ContDiffAt ℝ 2 g q ∧ ‖fderiv ℝ (fderiv ℝ g) q‖ ≤ K := by
   have hsm : ∀ᶠ q in 𝓝 (a,b), ContDiffAt ℝ 2 g q :=
     (hg.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)
   have hn := norm_eventually_bound (f := fderiv ℝ (fderiv ℝ g)) (x := (a,b)) (hessian_continuous hg)
   obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp (hsm.and hn)
   exact ⟨r,‖fderiv ℝ (fderiv ℝ g) (a,b)‖+1,hr,by positivity,
     fun q hq => ⟨(hrb hq).1,(hrb hq).2⟩⟩

 theorem smooth_quadratic_bound {g : E × F → ℝ} {c : E × F} {r K : ℝ}
     (hK : 0 ≤ K)
     (h : ∀ q ∈ Metric.ball c r, ContDiffAt ℝ 2 g q ∧ ‖fderiv ℝ (fderiv ℝ g) q‖ ≤ K)
     {x y : E} {p : F} (hx : (x,p) ∈ Metric.ball c r) (hy : (y,p) ∈ Metric.ball c r) :
     |g (y,p)-g (x,p)-fderiv ℝ g (x,p) (y-x,0)| ≤ K*‖y-x‖^2 := by
   have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
       (x,p)+t•((y-x,0) : E×F) ∈ Metric.ball c r := by
     have hh := (convex_ball c r) hx hy (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t = 1)
     have he : (x,p)+t•((y-x,0) : E×F) = (1-t)•(x,p)+t•(y,p) := by
       ext <;> simp only [Prod.smul_mk,Prod.mk_add_mk] <;> module
     exact he.symm ▸ hh
   obtain ⟨t,ht,he⟩ := MovingTaylor.second_segment (x,p) ((y-x,0) : E×F)
     (fun t ht => (h _ (hseg t ht)).1)
   have hvnorm : ‖((y-x,0) : E×F)‖ = ‖y-x‖ := by simp
   have hnorm := ContinuousLinearMap.le_opNorm₂
     (fderiv ℝ (fderiv ℝ g) ((x,p)+t•((y-x,0) : E×F))) ((y-x,0) : E×F) ((y-x,0) : E×F)
   have hb := (h _ (hseg t ⟨ht.1.le,ht.2.le⟩)).2
   have hxy : (x,p)+((y-x,0) : E×F) = (y,p) := by ext <;> simp
   rw [hxy] at he
   rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
   rw [hvnorm] at hnorm
   have hh : |fderiv ℝ (fderiv ℝ g) ((x,p)+t•((y-x,0) : E×F)) (y-x,0) (y-x,0)| ≤ K*‖y-x‖^2 := by
     have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖y-x‖)
     rw [Real.norm_eq_abs] at hnorm
     nlinarith
   nlinarith [mul_nonneg hK (sq_nonneg ‖y-x‖)]

 theorem two_sided_local {f : E → ℝ} {P Q : E → F} {g h : E×F → ℝ} {c : E}
     (hP : ContinuousAt P c) (hQ : ContinuousAt Q c)
     (hg : ContDiffAt ℝ ∞ g (c,P c)) (hh : ContDiffAt ℝ ∞ h (c,Q c))
     (hs : ∀ᶠ x in 𝓝 c, ∀ y : E,
       f x+h (y,Q x)-h (x,Q x) ≤ f y ∧ f y ≤ f x+g (y,P x)-g (x,P x)) :
     ContDiffAt ℝ 1 f c ∧ ∃ C : ℝ≥0, ∃ U ∈ 𝓝 c, LipschitzOnWith C (fderiv ℝ f) U := by
   obtain ⟨rg,Kg,hrg,hKg,hgb⟩ := smooth_local_bounds hg
   obtain ⟨rh,Kh,hrh,hKh,hhb⟩ := smooth_local_bounds hh
   have hp : ∀ᶠ x in 𝓝 c, dist (P x) (P c) < rg := hP (Metric.ball_mem_nhds _ hrg)
   have hq : ∀ᶠ x in 𝓝 c, dist (Q x) (Q c) < rh := hQ (Metric.ball_mem_nhds _ hrh)
   have hn : ∀ᶠ x in 𝓝 c, x ∈ Metric.ball c rg ∧ x ∈ Metric.ball c rh ∧
       dist (P x) (P c) < rg ∧ dist (Q x) (Q c) < rh ∧
       ∀ y : E, f x+h (y,Q x)-h (x,Q x) ≤ f y ∧ f y ≤ f x+g (y,P x)-g (x,P x) := by
     filter_upwards [Metric.ball_mem_nhds c hrg,Metric.ball_mem_nhds c hrh,hp,hq,hs] with x hx hy hp hq hs
     exact ⟨hx,hy,hp,hq,hs⟩
   obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp hn
   let L : E →L[ℝ] E×F := (ContinuousLinearMap.id ℝ E).prod 0
   let D (x : E) : E →L[ℝ] ℝ := (fderiv ℝ g (x,P x)).comp L
   have hgp (x y : E) (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) :
       (y,P x) ∈ Metric.ball (c,P c) rg := by
     rw [Metric.mem_ball,Prod.dist_eq]
     exact max_lt (hrb hy).1 (hrb hx).2.2.1
   have hhq (x y : E) (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) :
       (y,Q x) ∈ Metric.ball (c,Q c) rh := by
     rw [Metric.mem_ball,Prod.dist_eq]
     exact max_lt (hrb hy).2.1 (hrb hx).2.2.2.1
   have hD (x : E) (hx : x ∈ Metric.ball c r) : D x = (fderiv ℝ h (x,Q x)).comp L := by
     have hgd := ((hgb _ (hgp x x hx hx)).1.differentiableAt (by norm_num)).hasFDerivAt
     have hhd := ((hhb _ (hhq x x hx hx)).1.differentiableAt (by norm_num)).hasFDerivAt
     have hpx : HasFDerivAt (fun y : E => (y,P x)) L x :=
       (hasFDerivAt_id x).prodMk (hasFDerivAt_const (c := P x) x)
     have hqx : HasFDerivAt (fun y : E => (y,Q x)) L x :=
       (hasFDerivAt_id x).prodMk (hasFDerivAt_const (c := Q x) x)
     have hmin : IsLocalMin (fun y => g (y,P x)-h (y,Q x)) x := by
       apply Filter.Eventually.of_forall
       intro y
       have hsy := (hrb hx).2.2.2.2 y
       change g (x,P x)-h (x,Q x) ≤ g (y,P x)-h (y,Q x)
       linarith [hsy.1,hsy.2]
     have he := hmin.hasFDerivAt_eq_zero ((hgd.comp x hpx).sub (hhd.comp x hqx))
     exact sub_eq_zero.mp he
   apply c1_of_bound (D := D) hr (add_nonneg hKg hKh)
   intro x hx y hy
   have hg' := smooth_quadratic_bound hKg hgb (hgp x x hx hx) (hgp x y hx hy)
   have hh' := smooth_quadratic_bound hKh hhb (hhq x x hx hx) (hhq x y hx hy)
   have hs' := (hrb hx).2.2.2.2 y
   have hde : fderiv ℝ h (x,Q x) (y-x,0) = D x (y-x) :=
     congrArg (fun A : E →L[ℝ] ℝ => A (y-x)) (hD x hx).symm
   change |g (y,P x)-g (x,P x)-D x (y-x)| ≤ _ at hg'
   rw [hde] at hh'
   rw [abs_le] at hg' hh' ⊢
   have hn := sq_nonneg ‖y-x‖
   constructor <;> nlinarith [mul_nonneg hKg hn,mul_nonneg hKh hn]
end QuadraticEnvelope
end

end WeakMTWGlobalSupport

end OAI
