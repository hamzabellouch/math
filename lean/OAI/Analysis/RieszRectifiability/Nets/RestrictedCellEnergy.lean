import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cell_variance_le_energy_ae (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : 0 < μ.real univ)
    (E : X → X → ℝ) (C : ℝ)
    (hE : ∀ᵐ x ∂μ, Integrable (E x) μ)
    (hEE : Integrable (fun x => ∫ y, E x y ∂μ) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (w x - w y) ^ 2 ≤ C * E x y) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      C / (2 * μ.real univ) * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
  have hp : (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) ≤
      C * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
    calc
      _ ≤ ∫ x, C * (∫ y, E x y ∂μ) ∂μ := by
        apply integral_mono_ae (iterated_pairwise_square_integrable μ w hw) (hEE.const_mul C)
        filter_upwards [hE, hbound] with x hx hb
        calc
          _ ≤ ∫ y, C * E x y ∂μ :=
            integral_mono_ae (pairwise_square_integrable_right μ w hw x)
              (hx.const_mul C) hb
          _ = _ := integral_const_mul C (E x)
      _ = _ := integral_const_mul C _
  rw [cell_variance_eq_half_pairwise μ w hw hμ.ne']
  calc
    _ ≤ (C * (∫ x, ∫ y, E x y ∂μ ∂μ)) / (2 * μ.real univ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by ring

variable [MetricSpace X]

theorem restricted_cell_variance_le_fractional_energy (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) [IsFiniteMeasure (μ.restrict s)]
    (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 (μ.restrict s))
    (hμ : 0 < μ.real s) (r : ℝ)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2)
      ((μ.restrict s).prod (μ.restrict s))) :
    (∫ x in s, (w x - cellMean (μ.restrict s) w) ^ 2 ∂μ) ≤
      r ^ (m + 1) / (2 * μ.real s) *
        (∫ x in s, ∫ y in s, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  have hmass : 0 < (μ.restrict s).real univ := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using! hμ
  have h := cell_variance_le_energy_ae (μ.restrict s) w hw hmass
    (fractionalPairEnergy m w) (r ^ (m + 1)) hE.prod_right_ae hE.integral_prod_left
    (by
      filter_upwards [ae_restrict_mem hs] with x hx
      filter_upwards [ae_restrict_mem hs] with y hy
      exact square_le_radius_mul_fractional_energy m w x y r (hdiam x hx y hy))
  simpa only [Measure.real, Measure.restrict_apply_univ] using! h

theorem restricted_cell_variance_le_scale_times_energy (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) [IsFiniteMeasure (μ.restrict s)]
    (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 (μ.restrict s))
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : c * h ^ m ≤ μ.real s)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2)
      ((μ.restrict s).prod (μ.restrict s))) :
    (∫ x in s, (w x - cellMean (μ.restrict s) w) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ x in s, ∫ y in s, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  have hμ : 0 < μ.real s := lt_of_lt_of_le (by positivity) hmass
  exact (restricted_cell_variance_le_fractional_energy μ s hs m w hw hμ (a * h) hdiam hE).trans
    (mul_le_mul_of_nonneg_right (radius_mass_coefficient_le m a h c _ ha hh hc hmass)
      (integral_nonneg fun x => integral_nonneg fun y => fractionalPairEnergy_nonneg m w x y))

end

end RieszRectifiability

end OAI
