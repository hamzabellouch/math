import OAI.Geometry.CylinderCovering.Angular.CubicScaledFamily
import OAI.Geometry.CylinderCovering.Angular.CubicCost
import OAI.Geometry.CylinderCovering.Cubic.Similarity

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open Set TriangularCovering

theorem main_proof : MainStatement := by
  have hmin : minimumProjection4 = 4 * H := K4_projection_minimum
  refine ⟨hmin, 3208 * H, 1 / 100000, mul_pos (by norm_num) H_pos, by norm_num, ?_⟩
  intro ε hε hsmall
  obtain ⟨c, hcover, harea, hpres⟩ := finiteCover_proof ε hε hsmall
  refine ⟨c, hcover, hpres, harea, ?_, ?_⟩
  · rw [harea]
    have h := cubicCost_expansion hε hsmall
    have hid : cubicCost ε - (2 * H - H / 15 * ε ^ 2) =
        H * (cubicCost ε / H - (2 - ε ^ 2 / 15)) := by
      field_simp [H_ne_zero]
    rw [hid, abs_mul, abs_of_pos H_pos]
    nlinarith only [mul_le_mul_of_nonneg_left h H_pos.le]
  · intro hεsmall
    rw [harea, hmin]
    have h := cubicCost_strict hε hεsmall.le
    linarith

theorem scaledMain_proof : ScaledMainStatement := by
  refine ⟨401 / 4, 1 / 50000, by norm_num, by norm_num, ?_⟩
  intro τ hτ hsmall
  obtain ⟨c, hcover, harea, hpres⟩ := scaledFiniteCover_proof τ hτ hsmall
  refine ⟨c, hcover, hpres, harea, ?_, ?_⟩
  · rw [harea]
    have hid : cubicCost (τ / 2) / 4 / H = cubicCost (τ / 2) / (4 * H) := by ring
    rw [hid]
    exact scaled_cubicCost_expansion hτ hsmall
  · intro hτsmall
    rw [harea, TriangularCovering.main.1]
    have h := cubicCost_strict (show 0 < τ / 2 by linarith)
      (show τ / 2 ≤ 1 / 100000 by linarith)
    linarith

lemma relativeCost4_eq {m : ℕ} (c : Fin m → TriCylinder) :
    relativeCost4 c = relativeCost c / 4 := by
  unfold relativeCost4 relativeCost
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [K4_shadow]
  ring

lemma relativeCost4_lt_of_total_lt {m : ℕ} (c : Fin m → TriCylinder)
    (h : totalArea c < minimumProjection4 / 2) : relativeCost4 c < 1 / 2 := by
  have hmin : minimumProjection4 = 4 * H := K4_projection_minimum
  rw [hmin] at h
  have htotal : totalArea c / H < 2 := (div_lt_iff₀ H_pos).mpr (by linarith)
  have hrelative := relativeCost_le_totalArea c
  rw [relativeCost4_eq]
  linarith

lemma finiteFamily4_normalized {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100000) :
    relativeCost4 (finiteFamily4 ε hε) < 1 / 2 := by
  apply relativeCost4_lt_of_total_lt
  rw [finiteFamily4_total]
  have hmin : minimumProjection4 = 4 * H := K4_projection_minimum
  rw [hmin]
  have h := cubicCost_strict hε hsmall
  linarith

end CylinderCovering.Cubic

end

end OAI
