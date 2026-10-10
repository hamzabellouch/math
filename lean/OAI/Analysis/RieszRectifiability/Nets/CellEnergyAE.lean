import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PartitionEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function

variable {X ι : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype ι]

theorem cell_variance_le_fractional_energy_of_ae_diameter (μ : Measure X)
    [IsFiniteMeasure μ] (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (hμ : 0 < μ.real univ) (r : ℝ)
    (hdiam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ r)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      r ^ (m + 1) / (2 * μ.real univ) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  apply cell_variance_le_energy_ae μ w hw hμ (fractionalPairEnergy m w)
    (r ^ (m + 1)) hE.prod_right_ae hE.integral_prod_left
  filter_upwards [hdiam] with x hx
  filter_upwards [hx] with y hy
  exact square_le_radius_mul_fractional_energy m w x y r hy

theorem cell_variance_le_scale_times_energy_ae (μ : Measure X)
    [IsFiniteMeasure μ] (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : c * h ^ m ≤ μ.real univ)
    (hdiam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le (by positivity) hmass
  exact (cell_variance_le_fractional_energy_of_ae_diameter μ m w hw hμ
    (a * h) hdiam hE).trans
    (mul_le_mul_of_nonneg_right (radius_mass_coefficient_le m a h c _ ha hh hc hmass)
      (integral_nonneg fun x => integral_nonneg fun y => fractionalPairEnergy_nonneg m w x y))

theorem partition_error_le_scale_times_energy_ae (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : ∀ i, c * h ^ m ≤ μ.real (s i))
    (hdiam : ∀ i, ∀ᵐ x ∂μ.restrict (s i), ∀ᵐ y ∂μ.restrict (s i), dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x in ⋃ i, s i, (w x - partitionMean μ s w x) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ p : X × X, fractionalPairEnergy m w p.1 p.2 ∂μ.prod μ) := by
  have hi (i : ι) : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2)
      ((μ.restrict (s i)).prod (μ.restrict (s i))) := by
    rw [Measure.prod_restrict]
    exact hE.restrict
  have hm (i : ι) : c * h ^ m ≤ (μ.restrict (s i)).real univ := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using! hmass i
  rw [partition_error_eq_sum μ s hs hd w hw]
  calc
    _ ≤ ∑ i, (a ^ (m + 1) / (2 * c) * h) *
        (∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      Finset.sum_le_sum fun i _ => cell_variance_le_scale_times_energy_ae
        (μ.restrict (s i)) m w (hw.restrict (s i)) a h c ha hh hc (hm i) (hdiam i) (hi i)
    _ = (a ^ (m + 1) / (2 * c) * h) *
        (∑ i, ∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_cell_energy_le μ s hs hd _ hE (fun p => fractionalPairEnergy_nonneg m w p.1 p.2))
      (by positivity)

end

end RieszRectifiability

end OAI
