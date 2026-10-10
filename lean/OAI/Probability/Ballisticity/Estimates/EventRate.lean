import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
variable {X : Type*} [MeasurableSpace X]

lemma measure_le_liminf_of_ae_eventually (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (B : ℕ → Set X) (hB : ∀ k, MeasurableSet (B k))
    (he : ∀ᵐ x ∂μ, x∈A → ∀ᶠ k in atTop, x∈B k) :
    μ A≤liminf (fun k => μ (B k)) atTop := by
  calc
    μ A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by simp [hA]
    _ ≤ ∫⁻ x, liminf (fun k => (B k).indicator (fun _ => (1 : ℝ≥0∞)) x) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [he] with x hx
      by_cases ha : x∈A
      · rw [Set.indicator_of_mem ha]
        exact le_liminf_of_le (by isBoundedDefault) ((hx ha).mono fun k hk => by simp [hk])
      · simp [ha]
    _ ≤ liminf (fun k => ∫⁻ x, (B k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) atTop :=
      lintegral_liminf_le (fun k => measurable_const.indicator (hB k))
    _ = _ := by simp only [lintegral_indicator (hB _),lintegral_const,Measure.restrict_apply_univ,one_mul]

lemma event_rate (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) (B : ℕ → Set X) (hB : ∀ k, MeasurableSet (B k))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {a C M : ℝ} (ha : 0<a) (hC : 0≤C)
    (hbound : ∀ k, μ.real (B k)*(a*(ns k:ℝ))≤C*(ns k:ℝ)+M)
    (he : ∀ᵐ x ∂μ, x∈A → ∀ᶠ k in atTop, x∈B k) :
    μ.real A≤C/a := by
  have hn : ∀ᶠ k in atTop, 0<(ns k:ℝ) := by
    simpa only [Nat.cast_pos] using hns.eventually (eventually_gt_atTop 0)
  have hb : ∀ᶠ k in atTop, μ (B k)≤ENNReal.ofReal (C/a+(M/a)/(ns k:ℝ)) := by
    filter_upwards [hn] with k hk
    rw [←ENNReal.ofReal_toReal (measure_ne_top μ (B k))]
    apply ENNReal.ofReal_le_ofReal
    have hh := (le_div_iff₀ (mul_pos ha hk)).mpr (hbound k)
    calc
      _ ≤ (C*(ns k:ℝ)+M)/(a*(ns k:ℝ)) := hh
      _ = _ := by field_simp
  have ht : Tendsto (fun k => ENNReal.ofReal (C/a+(M/a)/(ns k:ℝ))) atTop (𝓝 (ENNReal.ofReal (C/a))) := by
    simpa only [Function.comp_def,add_zero] using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C/a)).add
      ((tendsto_const_div_atTop_nhds_zero_nat (M/a)).comp hns))
  have hh := (measure_le_liminf_of_ae_eventually μ A hA B hB he).trans
    ((liminf_le_liminf hb).trans_eq ht.liminf_eq)
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hC ha.le) hh

end DirectionalTransience

end

end OAI
