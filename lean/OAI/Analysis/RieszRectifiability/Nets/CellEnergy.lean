import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellVariance

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cell_variance_le_energy (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : 0 < μ.real univ)
    (E : X → X → ℝ) (C : ℝ)
    (hE : ∀ x, Integrable (E x) μ)
    (hEE : Integrable (fun x => ∫ y, E x y ∂μ) μ)
    (hbound : ∀ x y, (w x - w y) ^ 2 ≤ C * E x y) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      C / (2 * μ.real univ) * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
  have hp : (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) ≤
      C * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
    calc
      _ ≤ ∫ x, C * (∫ y, E x y ∂μ) ∂μ := by
        apply integral_mono (iterated_pairwise_square_integrable μ w hw) (hEE.const_mul C)
        intro x
        calc
          _ ≤ ∫ y, C * E x y ∂μ :=
            integral_mono (pairwise_square_integrable_right μ w hw x)
              ((hE x).const_mul C) (hbound x)
          _ = _ := integral_const_mul C (E x)
      _ = _ := integral_const_mul C _
  rw [cell_variance_eq_half_pairwise μ w hw hμ.ne']
  calc
    _ ≤ (C * (∫ x, ∫ y, E x y ∂μ ∂μ)) / (2 * μ.real univ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by ring

variable [MetricSpace X]

def fractionalPairEnergy (m : ℕ) (w : X → ℝ) (x y : X) : ℝ :=
  (w x - w y) ^ 2 / dist x y ^ (m + 1)

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

omit [MeasurableSpace X] in
theorem square_le_radius_mul_fractional_energy (m : ℕ) (w : X → ℝ)
    (x y : X) (r : ℝ) (hxy : dist x y ≤ r) :
    (w x - w y) ^ 2 ≤ r ^ (m + 1) * fractionalPairEnergy m w x y := by
  by_cases heq : x = y
  · simp [heq, fractionalPairEnergy]
  have hd : 0 < dist x y := dist_pos.mpr heq
  have hp := pow_le_pow_left₀ (dist_nonneg (x := x) (y := y)) hxy (m + 1)
  unfold fractionalPairEnergy
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hd (m + 1))).2
  calc
    _ = dist x y ^ (m + 1) * (w x - w y) ^ 2 := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (sq_nonneg _)

theorem cell_variance_le_fractional_energy (μ : Measure X) [IsFiniteMeasure μ]
    (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : 0 < μ.real univ)
    (r : ℝ) (hdiam : ∀ x y : X, dist x y ≤ r)
    (hE : ∀ x, Integrable (fractionalPairEnergy m w x) μ)
    (hEE : Integrable (fun x => ∫ y, fractionalPairEnergy m w x y ∂μ) μ) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      r ^ (m + 1) / (2 * μ.real univ) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) :=
  cell_variance_le_energy μ w hw hμ _ _ hE hEE
    (fun x y => square_le_radius_mul_fractional_energy m w x y r (hdiam x y))

theorem radius_mass_coefficient_le (m : ℕ) (a h c M : ℝ)
    (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c) (hM : c * h ^ m ≤ M) :
    (a * h) ^ (m + 1) / (2 * M) ≤ a ^ (m + 1) / (2 * c) * h := by
  calc
    _ ≤ (a * h) ^ (m + 1) / (2 * (c * h ^ m)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by
      rw [mul_pow, pow_succ h m]
      field_simp

theorem cell_variance_le_scale_times_energy (μ : Measure X) [IsFiniteMeasure μ]
    (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : c * h ^ m ≤ μ.real univ)
    (hdiam : ∀ x y : X, dist x y ≤ a * h)
    (hE : ∀ x, Integrable (fractionalPairEnergy m w x) μ)
    (hEE : Integrable (fun x => ∫ y, fractionalPairEnergy m w x y ∂μ) μ) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le (by positivity) hmass
  exact (cell_variance_le_fractional_energy μ m w hw hμ (a * h) hdiam hE hEE).trans
    (mul_le_mul_of_nonneg_right (radius_mass_coefficient_le m a h c _ ha hh hc hmass)
      (integral_nonneg fun x => integral_nonneg fun y =>
        fractionalPairEnergy_nonneg m w x y))

end

end RieszRectifiability

end OAI
