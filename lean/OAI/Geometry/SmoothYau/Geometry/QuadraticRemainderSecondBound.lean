import Mathlib

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

lemma quadratic_remainder_of_second_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖^2 := by
  have hdf := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have hL (z : E) : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C*‖z-x‖ :=
    (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf.differentiable (by simp) z) (fun z _ => hb z) (mem_univ x) (mem_univ z)
  let R := fun z => f z - f x - fderiv ℝ f x (z-x)
  have hR (z : E) : HasFDerivAt R (fderiv ℝ f z - fderiv ℝ f x) z := by
    convert ((hf.differentiable (by simp) z).hasFDerivAt.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)) using 1 <;> rfl
  have hrbound (z : E) (hz : z ∈ closedBall x ‖y-x‖) :
      ‖fderiv ℝ R z‖ ≤ C*‖y-x‖ := by
    rw [(hR z).fderiv]
    exact (hL z).trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hz) hC)
  have hh := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hR z).differentiableAt) hrbound
    (mem_closedBall_self (norm_nonneg _))
    (show y ∈ closedBall x ‖y-x‖ by simp [dist_eq_norm])
  simpa only [R,sub_self,map_zero,sub_zero,pow_two,mul_assoc] using hh

theorem cutoff_gradient_square_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 < C)
    (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x : E) :
    ‖fderiv ℝ f x‖^2 ≤ 4*C*f x := by
  let v := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hv : ‖v‖ = ‖fderiv ℝ f x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hd : fderiv ℝ f x v = ‖v‖^2 := by
    rw [←InnerProductSpace.toDual_symm_apply]
    exact real_inner_self_eq_norm_sq v
  let t : ℝ := (2*C)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  have htc : t*(2*C) = 1 := inv_mul_cancel₀ (by positivity)
  have he := quadratic_remainder_of_second_bound hf hC.le hb x (x-t • v)
  have hyn := hn (x-t • v)
  have hs : x-t • v-x = -(t • v) := by abel
  simp only [hs,map_neg,map_smul,smul_eq_mul,hd,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_pos ht] at he
  have hupper := (le_abs_self (f (x-t • v)-f x- -(t*‖v‖^2))).trans he
  have hsmall : t*‖v‖^2 ≤ f x+C*t^2*‖v‖^2 := by nlinarith
  have hcoeff : C*t^2 = t/2 := by nlinarith [htc]
  rw [hcoeff] at hsmall
  have hres : ‖v‖^2 ≤ 4*C*f x := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2*C by positivity)
    nlinarith [htc]
  simpa only [hv] using hres

theorem exists_cutoff_sqrt_gradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hn : ∀ x, 0 ≤ f x) :
    ∃ C > 0, ∀ x, ‖fderiv ℝ f x‖ ≤ C * Real.sqrt (f x) := by
  have hd := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have hdd := hd.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  obtain ⟨B,hB⟩ := hdd.continuous.bounded_above_of_compact_support ((hs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Real.sqrt (4*C),Real.sqrt_pos.mpr (by positivity),fun x => ?_⟩
  have hh := cutoff_gradient_square_bound hf hn hC (fun y => (hB y).trans (le_max_left _ _)) x
  have hs1 := Real.sq_sqrt (show 0 ≤ 4*C by positivity)
  have hs2 := Real.sq_sqrt (hn x)
  have hp : 0 ≤ Real.sqrt (4*C)*Real.sqrt (f x) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (‖fderiv ℝ f x‖ + Real.sqrt (4*C)*Real.sqrt (f x))]
end YauCounterexamples

end

end OAI
