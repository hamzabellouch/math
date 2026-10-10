import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Cutoff

namespace OAI

noncomputable section
namespace VelocityDetection.Cutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Filter
open scoped Topology ContDiff

theorem spatialD_cutoff_zero_of_large {R : ℝ} (hR : 0 < R) {Y : Coord 2}
    (hY : ∃ j, R ≤ |Y j|) (i : Fin 2) (t : ℝ) :
    spatialD i (fun _ X => cutoff R X) t Y = 0 := by
  obtain ⟨j, hj⟩ := hY
  have hb : 1 ≤ |Y j / R| := by
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR, one_mul]
    exact hj
  fin_cases i <;> fin_cases j
  · change 1 ≤ |Y 0 / R| at hb
    change spatialD 0 (fun _ X => cutoff R X) t Y = 0
    simp only [spatialD_cutoff_zero, profileD_zero hb, zero_div, zero_mul]
  · change 1 ≤ |Y 1 / R| at hb
    change spatialD 0 (fun _ X => cutoff R X) t Y = 0
    simp only [spatialD_cutoff_zero, profile_zero hb, mul_zero]
  · change 1 ≤ |Y 0 / R| at hb
    change spatialD 1 (fun _ X => cutoff R X) t Y = 0
    simp only [spatialD_cutoff_one, profile_zero hb, zero_mul]
  · change 1 ≤ |Y 1 / R| at hb
    change spatialD 1 (fun _ X => cutoff R X) t Y = 0
    simp only [spatialD_cutoff_one, profileD_zero hb, zero_div, mul_zero]

end VelocityDetection.Cutoff
end

noncomputable section
namespace VelocityDetection.Cutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Filter
open scoped Topology ContDiff
open MeasureTheory

theorem integral_laplacian_mul_lower {R ν : ℝ} (hR : 0 < R) (hν : 0 ≤ ν)
    (c : Coord 2) {ρ : Coord 2 → ℝ} (hρ : Integrable ρ) (hρ0 : ∀ X, 0 ≤ ρ X)
    (hmass : (∫ X, ρ X) ≤ 1) :
    -(ν * 3000 / R ^ 2) ≤
      ν * ∫ X, laplacian (fun _ Y => cutoff R Y) 0 (X - c) * ρ X := by
  let B : ℝ := 3000 / R ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf : Continuous (fun X => laplacian (fun _ Y => cutoff R Y) 0 (X - c)) :=
    (continuous_laplacian_cutoff R 0).comp (continuous_id.sub continuous_const)
  have hint : Integrable (fun X => laplacian (fun _ Y => cutoff R Y) 0 (X - c) * ρ X) :=
    hρ.bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun X =>
      by simpa only [Real.norm_eq_abs] using laplacian_cutoff_bound_3000 hR 0 (X - c)))
  have hi : (∫ X, (-B) * ρ X) ≤
      ∫ X, laplacian (fun _ Y => cutoff R Y) 0 (X - c) * ρ X := by
    apply integral_mono (hρ.const_mul _) hint
    intro X
    exact mul_le_mul_of_nonneg_right (abs_le.mp (laplacian_cutoff_bound_3000 hR 0 (X - c))).1 (hρ0 X)
  rw [integral_const_mul] at hi
  have hm : -B ≤ (-B) * ∫ X, ρ X := by nlinarith
  have hle := mul_le_mul_of_nonneg_left (hm.trans hi) hν
  calc
    -(ν * 3000 / R ^ 2) = ν * -B := by dsimp [B]; ring
    _ ≤ _ := hle

end VelocityDetection.Cutoff
end

end OAI
