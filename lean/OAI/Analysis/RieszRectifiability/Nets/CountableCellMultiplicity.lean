import Mathlib

namespace OAI

/-!
# Countable cell multiplicity

The sum of cell indicators measures pointwise overlap. Its integral is the total
cell mass, giving tail bounds, almost-everywhere finite incidence, and lower
bounds for the mass where the multiplicity is controlled.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def cellMultiplicity {ι X : Type*} (A : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x

theorem cellMultiplicity_measurable {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (cellMultiplicity A) :=
  Measurable.tsum (fun i => measurable_const.indicator (hA i))

theorem lintegral_cellMultiplicity {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    (∫⁻ x, cellMultiplicity A x ∂μ) = ∑' i, μ (A i) := by
  unfold cellMultiplicity
  rw [lintegral_tsum
    (fun i => (measurable_const.indicator (hA i)).aemeasurable)]
  exact tsum_congr (fun i => lintegral_indicator_one (hA i))

theorem cellMultiplicity_tail_bound {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (B t : ℝ≥0∞) (hB : ∑' i, μ (A i) ≤ B) (ht : t ≠ 0) (htt : t ≠ ∞) :
    μ {x | t ≤ cellMultiplicity A x} ≤ B / t := by
  have h := meas_ge_le_lintegral_div (μ := μ)
    (cellMultiplicity_measurable A hA).aemeasurable ht htt
  rw [lintegral_cellMultiplicity μ A hA] at h
  exact h.trans (ENNReal.div_le_div_right hB t)

theorem ae_finite_cell_incidence {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hfinite : ∑' i, μ (A i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ A i}.Finite := by
  classical
  have hint : (∫⁻ x, cellMultiplicity A x ∂μ) ≠ ∞ := by
    rwa [lintegral_cellMultiplicity μ A hA]
  filter_upwards [ae_lt_top (cellMultiplicity_measurable A hA) hint] with x hx
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hx.ne (ε := 1) one_ne_zero
  apply hf.subset
  intro i hi
  change x ∈ A i at hi
  change 1 ≤ (A i).indicator (fun _ => (1 : ℝ≥0∞)) x
  rw [Set.indicator_of_mem hi]

theorem cellMultiplicity_good_mass_lower {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (T : Set X) (B t : ℝ≥0∞) (hB : ∑' i, μ (A i) ≤ B) (ht : t ≠ 0) (htt : t ≠ ∞) :
    μ T - B / t ≤ μ {x ∈ T | cellMultiplicity A x < t} := by
  have htail := cellMultiplicity_tail_bound μ A hA B t hB ht htt
  calc
    μ T - B / t ≤ μ T - μ {x | t ≤ cellMultiplicity A x} := tsub_le_tsub_left htail _
    _ ≤ μ (T \ {x | t ≤ cellMultiplicity A x}) := le_measure_sdiff
    _ = _ := by congr 1; ext x; simp only [mem_sdiff, mem_ofPred_eq, not_le]

theorem cellMultiplicity_half_mass {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (T : Set X) (K : ℝ≥0∞) (hK : K ≠ 0) (hKt : K ≠ ∞) (hT : μ T ≠ ∞)
    (hB : ∑' i, μ (A i) ≤ K * μ T) :
    μ T / 2 ≤ μ {x ∈ T | cellMultiplicity A x < K * 2} := by
  have hg := cellMultiplicity_good_mass_lower μ A hA T (K * μ T) (K * 2) hB
    (mul_ne_zero hK (by norm_num)) (ENNReal.mul_ne_top hKt (by norm_num))
  rwa [ENNReal.mul_div_mul_left _ _ hK hKt, ENNReal.sub_half hT] at hg

end

end RieszRectifiability

end OAI
