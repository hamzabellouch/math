import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology NNReal
namespace QuadraticEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hasFDerivAt_of_bound {f : E → ℝ} {D : E →L[ℝ] ℝ} {x : E} {K : ℝ}
     (h : ∀ᶠ y in 𝓝 x, |f y-f x-D (y-x)| ≤ K*‖y-x‖^2) : HasFDerivAt f D x := by
   rw [hasFDerivAt_iff_isLittleO]
   apply (Asymptotics.IsBigO.of_bound K ?_).trans_isLittleO
     (Asymptotics.isLittleO_pow_sub_sub x (show 1 < 2 from by norm_num))
   filter_upwards [h] with y hy
   simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hy

 theorem differential_lipschitz {f : E → ℝ} {D : E → E →L[ℝ] ℝ} {c : E} {r K : ℝ}
     (hr : 0 < r) (hK : 0 ≤ K)
     (h : ∀ x ∈ Metric.ball c r, ∀ y ∈ Metric.ball c r,
       |f y-f x-D x (y-x)| ≤ K*‖y-x‖^2) :
     LipschitzOnWith ⟨6*K,by positivity⟩ D (Metric.ball c (r/4)) := by
   apply LipschitzOnWith.of_dist_le_mul
   intro x hx y hy
   rw [dist_eq_norm]
   change ‖D x-D y‖ ≤ (6*K)*dist x y
   by_cases he : x = y
   · subst y; simp
   have hd : 0 < dist x y := dist_pos.mpr he
   change dist x c < r/4 at hx
   change dist y c < r/4 at hy
   have hx' : x ∈ Metric.ball c r := by
     change dist x c < r
     linarith
   have hy' : y ∈ Metric.ball c r := by
     change dist y c < r
     linarith
   have hdist : dist x y < r/2 := by
     calc
       dist x y ≤ dist x c+dist y c := dist_triangle_right x y c
       _ < r/2 := by linarith [hx,hy]
   apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
   intro e he
   let z := y+(dist x y)•e
   have hzy : ‖z-y‖ = dist x y := by
     simp only [z,add_sub_cancel_left,norm_smul,he,Real.norm_eq_abs,abs_of_nonneg dist_nonneg,mul_one]
   have hzx : ‖z-x‖ ≤ 2*dist x y := by
     calc
       ‖z-x‖ = ‖(z-y)+(y-x)‖ := by congr 1; abel
       _ ≤ ‖z-y‖+‖y-x‖ := norm_add_le _ _
       _ = 2*dist x y := by rw [hzy,← dist_eq_norm,dist_comm]; ring
   have hz : z ∈ Metric.ball c r := by
     calc
       dist z c ≤ dist z y+dist y c := dist_triangle _ _ _
       _ < r := by rw [dist_eq_norm z y,hzy]; linarith [hy]
   have hxy := h x hx' y hy'
   have hxz := h x hx' z hz
   have hyz := h y hy' z hz
   have heq : (D x-D y) (z-y) =
       (f z-f y-D y (z-y))-(f z-f x-D x (z-x))+(f y-f x-D x (y-x)) := by
     simp only [sub_apply,map_sub]
     ring
   have hh : |(D x-D y) (z-y)| ≤ 6*K*(dist x y)^2 := by
     rw [heq]
     calc
       _ ≤ |f z-f y-D y (z-y)|+|f z-f x-D x (z-x)|+|f y-f x-D x (y-x)| := by
         calc
           _ ≤ |(f z-f y-D y (z-y))-(f z-f x-D x (z-x))|+|f y-f x-D x (y-x)| := abs_add_le _ _
           _ ≤ |f z-f y-D y (z-y)|+|f z-f x-D x (z-x)|+|f y-f x-D x (y-x)| :=
             add_le_add (abs_sub (f z-f y-D y (z-y)) (f z-f x-D x (z-x))) (le_refl _)
       _ ≤ K*‖z-y‖^2+K*‖z-x‖^2+K*‖y-x‖^2 := add_le_add (add_le_add hyz hxz) hxy
       _ ≤ 6*K*(dist x y)^2 := by
         rw [hzy,← dist_eq_norm y x,dist_comm y x]
         have hh : ‖z-x‖^2 ≤ (2*dist x y)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hzx
         nlinarith [mul_le_mul_of_nonneg_left hh hK]
   have hh' : dist x y * |(D x-D y) e| ≤ dist x y * (6*K*dist x y) := by
     simp only [z,add_sub_cancel_left,map_smul,smul_eq_mul,abs_mul,
       abs_of_nonneg dist_nonneg] at hh
     nlinarith [hh]
   change |(D x-D y) e| ≤ 6*K*dist x y
   nlinarith [hh']

 theorem c1_of_bound {f : E → ℝ} {D : E → E →L[ℝ] ℝ} {c : E} {r K : ℝ}
     (hr : 0 < r) (hK : 0 ≤ K)
     (h : ∀ x ∈ Metric.ball c r, ∀ y ∈ Metric.ball c r,
       |f y-f x-D x (y-x)| ≤ K*‖y-x‖^2) :
     ContDiffAt ℝ 1 f c ∧ ∃ C : ℝ≥0, ∃ U ∈ 𝓝 c, LipschitzOnWith C (fderiv ℝ f) U := by
   have hd (x : E) (hx : x ∈ Metric.ball c r) : HasFDerivAt f (D x) x :=
     hasFDerivAt_of_bound (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) (h x hx))
   have hsub : Metric.ball c (r/4) ⊆ Metric.ball c r := Metric.ball_subset_ball (by linarith)
   have hLip := differential_lipschitz hr hK h
   refine ⟨contDiffAt_one_iff.mpr ⟨D,Metric.ball c (r/4),Metric.ball_mem_nhds c (by positivity),
     hLip.continuousOn,fun x hx => hd x (hsub hx)⟩,⟨6*K,by positivity⟩,
     Metric.ball c (r/4),Metric.ball_mem_nhds c (by positivity),?_⟩
   apply LipschitzOnWith.of_dist_le_mul
   intro x hx y hy
   rw [(hd x (hsub hx)).fderiv,(hd y (hsub hy)).fderiv]
   exact hLip.dist_le_mul x hx y hy
end QuadraticEnvelope
end

end WeakMTWGlobalSupport

end OAI
