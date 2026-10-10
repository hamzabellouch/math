import OAI.Analysis.CircleDomains.Probability.MeasureFamilyNullUnions
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! Removing a pointwise zero-modulus family does not alter modulus.
Minkowski's inequality controls the arbitrarily cheap admissible repair. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_le_admissible_off_null_family
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : Set A) (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0)
    {h : Z → ℝ≥0∞} (hh : Measurable h)
    (ha : ∀ a, a ∉ S → 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, h z ^ 2 ∂σ := by
  have hroot : (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
      (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    have hδ2 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞)^2 := by positivity
    obtain ⟨g,hg,hga,hge⟩ := (measureFamilyModulus_zero_iff σ
      (fun a : S => K a.val)).mp hS _ hδ2
    have hsum : ∀ a, 1 ≤ ∫⁻ z, h z + g z ∂(K a : Measure Z) := by
      intro a
      by_cases has : a ∈ S
      · exact (hga ⟨a,has⟩).trans (lintegral_mono (fun _ => le_add_self))
      · exact (ha a has).trans (lintegral_mono (fun _ => le_self_add))
    have hnorm := ENNReal.lintegral_Lp_add_le (μ := σ) hh.aemeasurable hg.aemeasurable
      (p := (2 : ℝ)) (by norm_num)
    have hgroot : (∫⁻ z, g z ^ 2 ∂σ) ^ (1/2 : ℝ) ≤ δ := by
      have hle := ENNReal.rpow_le_rpow hge.le (by norm_num : (0 : ℝ) ≤ 1/2)
      simpa only [← ENNReal.rpow_two,← ENNReal.rpow_mul,
        show (2 : ℝ)*(1/2)=1 by norm_num,ENNReal.rpow_one] using hle
    calc
      (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
          (∫⁻ z, (h z+g z)^2 ∂σ) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (measureFamilyModulus_le_admissible σ K (hh.add hg) hsum)
          (by norm_num)
      _ ≤ (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) +
          (∫⁻ z, g z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
        simpa only [Pi.add_apply,ENNReal.rpow_two] using hnorm
      _ ≤ (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) + δ := add_le_add_right hgroot _
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1/2)).mp hroot

lemma measureFamilyModulus_remove_null_family
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : Set A) (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K =
      measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val) := by
  apply le_antisymm
  · apply le_iInf
    intro h
    apply le_iInf
    intro hh
    apply le_iInf
    intro ha
    exact measureFamilyModulus_le_admissible_off_null_family σ K S hS hh
      (fun a has => ha ⟨a,has⟩)
  · apply measureFamilyModulus_mono_range
    rintro v ⟨a,rfl⟩
    exact mem_range_self a.val

end CircleDomainRigidity

end

end OAI
