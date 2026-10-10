import OAI.Geometry.CylinderCovering.Angular.CubicCoverDefinitions
import OAI.Geometry.CylinderCovering.Angular.CubicArea

namespace OAI

open Set Filter Asymptotics
open scoped Topology

noncomputable section
namespace CylinderCovering.Cubic
open TriangularCovering

lemma cubicCost_eq_areaSum (eps : ℝ) : cubicCost eps = H * areaSum eps (n eps) := by
  unfold cubicCost areaSum areaTerm speedSq
  simp only [node_succ]

lemma cubicCost_div_H (eps : ℝ) : cubicCost eps / H = areaSum eps (n eps) := by
  rw [cubicCost_eq_areaSum]
  have hH : H ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  field_simp

theorem cubicCost_expansion {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1 / 2) :
    |cubicCost eps / H - (2 - eps ^ 2 / 15)| ≤ 3208 * eps ^ 3 := by
  rw [cubicCost_div_H]
  exact areaSum_expansion he0.le he1 (ceil_count_pos he0) (ceil_step_le he0)

theorem cubicCost_strict {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1 / 100000) :
    cubicCost eps < 2 * H := by
  have hehalf : eps ≤ 1 / 2 := by linarith
  have hbound := (abs_le.mp (cubicCost_expansion he0 hehalf)).2
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos he0
  have he3 : eps ^ 3 ≤ eps ^ 2 / 100000 := by
    nlinarith only [mul_le_mul_of_nonneg_right he1 he2.le]
  have hratio : cubicCost eps / H < 2 := by nlinarith only [hbound, he2, he3]
  have hH : 0 < H := Real.sqrt_pos.2 (by norm_num)
  exact (div_lt_iff₀ hH).mp hratio

theorem cubicCost_bigO :
    (fun eps : ℝ => cubicCost eps - (2 * H - H / 15 * eps ^ 2))
      =O[𝓝[>] (0 : ℝ)] (fun eps => eps ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (3208 * H)
  have hsmall : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), eps < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with eps he0 he1
  have h := cubicCost_expansion he0 he1.le
  have hH : 0 < H := Real.sqrt_pos.2 (by norm_num)
  have hid : cubicCost eps - (2 * H - H / 15 * eps ^ 2) =
      H * (cubicCost eps / H - (2 - eps ^ 2 / 15)) := by
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hid, abs_mul, abs_of_pos hH,
    abs_of_nonneg (show 0 ≤ eps ^ 3 from pow_nonneg he0.le 3)]
  nlinarith only [mul_le_mul_of_nonneg_left h hH.le]

theorem scaled_cubicCost_expansion {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau ≤ 1) :
    |cubicCost (tau / 2) / (4 * H) - (1 / 2 - tau ^ 2 / 240)| ≤
      (401 / 4 : ℝ) * tau ^ 3 := by
  have h := cubicCost_expansion (show 0 < tau / 2 by linarith)
    (show tau / 2 ≤ 1 / 2 by linarith)
  have hH : H ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hid : cubicCost (tau / 2) / (4 * H) - (1 / 2 - tau ^ 2 / 240) =
      (cubicCost (tau / 2) / H - (2 - (tau / 2) ^ 2 / 15)) / 4 := by
    field_simp
    ring
  rw [hid, abs_div]
  norm_num
  nlinarith only [h]

lemma scaled_ceil_count {tau : ℝ} (ht : 0 < tau) :
    n (tau / 2) = ⌈8 / tau ^ 2⌉₊ := by
  unfold n
  congr 1
  field_simp
  ring

lemma scaled_cap (tau a b : ℝ) :
    cap (tau / 2) a b / 2 =
      1 / 2 + tau ^ 2 * (profileMax a b / 8 + (25 / 4 : ℝ) * tau) := by
  unfold cap
  ring

end CylinderCovering.Cubic

end

end OAI
