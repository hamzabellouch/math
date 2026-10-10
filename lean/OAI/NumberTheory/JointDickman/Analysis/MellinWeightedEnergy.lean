import OAI.NumberTheory.JointDickman.Analysis.MellinSpectralWeights

namespace OAI

/-! # From interval Dirichlet energies to a Schwartz weighted energy -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap

/-- The constant depends only on the fixed Schwartz window. A bound linear
in the frequency cutoff gives a finite weighted energy, without a logarithmic
loss from the number of frequency intervals. -/
theorem schwartz_weighted_energy_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℂ), Continuous F → ∀ A B : ℝ,
      0 ≤ A → 0 ≤ B →
      Integrable (fun t : ℝ => ‖w t‖ ^ 2 * ‖F t‖ ^ 2) →
      (∀ T : ℝ, 1 ≤ T → (∫ t in -T..T, ‖F t‖ ^ 2) ≤ A + B * T) →
      (∫ t : ℝ, ‖w t‖ ^ 2 * ‖F t‖ ^ 2) ≤ C * (A + B) := by
  obtain ⟨K, hK, hweight⟩ := schwartz_cell_norm_sq_bound w
  let W : ℝ := ∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ 3
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨2 * K * W + 1, by positivity, ?_⟩
  intro F hF A B hA hB hI henergy
  let G : ℝ → ℝ := fun t => ‖w t‖ ^ 2 * ‖F t‖ ^ 2
  have hG : Continuous G := (w.continuous.norm.pow 2).mul (hF.norm.pow 2)
  have hcell (n : ℤ) :
      (∫ t in (n : ℝ)..n + 1, G t) ≤
        (2 * K * (A + B)) * (1 / (1 + |(n : ℝ)|) ^ 3) := by
    let q : ℝ := 1 + |(n : ℝ)|
    let T : ℝ := |(n : ℝ)| + 2
    have hq : 0 < q := by dsimp [q]; linarith [abs_nonneg (n : ℝ)]
    have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg (n : ℝ)]
    have hnT : -T ≤ (n : ℝ) := by dsimp [T]; linarith [neg_abs_le (n : ℝ)]
    have hnT' : (n : ℝ) + 1 ≤ T := by dsimp [T]; linarith [le_abs_self (n : ℝ)]
    have hmean : (∫ t in (n : ℝ)..n + 1, ‖F t‖ ^ 2) ≤ A + B * T :=
      (intervalIntegral.integral_mono_interval hnT (by linarith) hnT'
        (Filter.Eventually.of_forall (fun t => sq_nonneg ‖F t‖))
        ((hF.norm.pow 2).intervalIntegrable (-T) T)).trans (henergy T hT)
    have hlinear : A + B * T ≤ 2 * (A + B) * q := by
      have hq1 : 1 ≤ q := by dsimp [q]; linarith [abs_nonneg (n : ℝ)]
      have hAq := mul_le_mul_of_nonneg_left hq1 hA
      have hBq := mul_le_mul_of_nonneg_left hq1 hB
      dsimp [q, T] at *
      nlinarith
    calc
      _ ≤ ∫ t in (n : ℝ)..n + 1, (K / q ^ 4) * ‖F t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hG.intervalIntegrable _ _) ((continuous_const.mul (hF.norm.pow 2)).intervalIntegrable _ _)
        intro t ht
        exact mul_le_mul_of_nonneg_right (hweight n t ht.1 ht.2) (sq_nonneg _)
      _ = (K / q ^ 4) * (∫ t in (n : ℝ)..n + 1, ‖F t‖ ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (K / q ^ 4) * (A + B * T) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ ≤ (K / q ^ 4) * (2 * (A + B) * q) :=
        mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = _ := by dsimp [q]; field_simp
  have hsum := hI.hasSum_intervalIntegral 0
  have hsum' : HasSum (fun n : ℤ => ∫ t in (n : ℝ)..n + 1, G t) (∫ t, G t) := by
    simpa only [zero_add] using hsum
  have hmajor := summable_integer_window_weights.mul_left (2 * K * (A + B))
  calc
    _ = ∑' n : ℤ, ∫ t in (n : ℝ)..n + 1, G t := hsum'.tsum_eq.symm
    _ ≤ ∑' n : ℤ, (2 * K * (A + B)) * (1 / (1 + |(n : ℝ)|) ^ 3) :=
      hsum'.summable.tsum_le_tsum hcell hmajor
    _ = (2 * K * (A + B)) * W := tsum_mul_left
    _ ≤ (2 * K * W + 1) * (A + B) := by nlinarith

end JointDickman

end OAI
