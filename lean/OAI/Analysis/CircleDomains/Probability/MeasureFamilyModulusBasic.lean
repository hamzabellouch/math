import OAI.Analysis.CircleDomains.Probability.PublishedMeasureDuality
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Pointwise measure-family modulus: monotonicity, indexing invariance,
and the zero-modulus family of measures charging a fixed reference-null set.
Extended-valued admissible densities are retained throughout. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {A B Z : Type*} [MeasurableSpace Z]

lemma measureFamilyModulus_le_admissible (σ : Measure Z) (K : A → FiniteMeasure Z)
    {h : Z → ℝ≥0∞} (hh : Measurable h)
    (ha : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, h z ^ 2 ∂σ :=
  iInf_le_of_le h (iInf_le_of_le hh (iInf_le_of_le ha le_rfl))

lemma exists_admissible_of_modulus_lt (σ : Measure Z) (K : A → FiniteMeasure Z)
    {ε : ℝ≥0∞} (hε : measureFamilyModulus A Z σ K < ε) :
    ∃ h : Z → ℝ≥0∞, Measurable h ∧
      (∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) ∧ (∫⁻ z, h z ^ 2 ∂σ) < ε := by
  simpa only [measureFamilyModulus,iInf_lt_iff,exists_prop] using hε

lemma measureFamilyModulus_zero_iff (σ : Measure Z) (K : A → FiniteMeasure Z) :
    measureFamilyModulus A Z σ K = 0 ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ h : Z → ℝ≥0∞, Measurable h ∧
        (∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) ∧ (∫⁻ z, h z ^ 2 ∂σ) < ε := by
  constructor
  · intro hm ε hε
    exact exists_admissible_of_modulus_lt σ K (hm ▸ hε)
  · intro he
    by_contra hm
    obtain ⟨h,hh,ha,hsmall⟩ := he (measureFamilyModulus A Z σ K) (pos_iff_ne_zero.mpr hm)
    exact (not_lt_of_ge (measureFamilyModulus_le_admissible σ K hh ha)) hsmall

lemma measureFamilyModulus_mono_range (σ : Measure Z)
    (K : A → FiniteMeasure Z) (L : B → FiniteMeasure Z) (hKL : range K ⊆ range L) :
    measureFamilyModulus A Z σ K ≤ measureFamilyModulus B Z σ L := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  apply measureFamilyModulus_le_admissible σ K hh
  intro a
  obtain ⟨b,hb⟩ := hKL (mem_range_self a)
  simpa only [hb] using ha b

lemma measureFamilyModulus_eq_of_range_eq (σ : Measure Z)
    (K : A → FiniteMeasure Z) (L : B → FiniteMeasure Z) (hKL : range K = range L) :
    measureFamilyModulus A Z σ K = measureFamilyModulus B Z σ L :=
  le_antisymm (measureFamilyModulus_mono_range σ K L hKL.subset)
    (measureFamilyModulus_mono_range σ L K hKL.symm.subset)

lemma measureFamilyModulus_mono_reference {σ τ : Measure Z} (hστ : σ ≤ τ)
    (K : A → FiniteMeasure Z) :
    measureFamilyModulus A Z σ K ≤ measureFamilyModulus A Z τ K := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  exact (measureFamilyModulus_le_admissible σ K hh ha).trans
    (lintegral_mono' hστ le_rfl)

lemma measureFamilyModulus_zero_of_charges_null_set
    (σ : Measure Z) (K : A → FiniteMeasure Z) {N : Set Z}
    (hN : MeasurableSet N) (hσN : σ N = 0) (hK : ∀ a, (K a : Measure Z) N ≠ 0) :
    measureFamilyModulus A Z σ K = 0 := by
  let h : Z → ℝ≥0∞ := N.indicator (fun _ => ∞)
  have hh : Measurable h := measurable_const.indicator hN
  have ha (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    rw [lintegral_indicator hN]
    simp [lintegral_const, hK a]
  have he : ∫⁻ z, h z ^ 2 ∂σ = 0 := by
    have hp : (fun z => h z ^ 2) = h := by
      funext z
      by_cases hz : z ∈ N <;> simp [h,hz]
    rw [hp,lintegral_indicator hN]
    simp [lintegral_const,hσN]
  exact le_antisymm (he ▸ measureFamilyModulus_le_admissible σ K hh ha) bot_le

end CircleDomainRigidity

end

end OAI
