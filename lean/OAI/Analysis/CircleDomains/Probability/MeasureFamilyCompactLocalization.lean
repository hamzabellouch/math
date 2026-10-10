import OAI.Analysis.CircleDomains.Probability.FiniteMeasureTightControl
import OAI.Analysis.CircleDomains.Probability.MeasureFamilySubadditivity

namespace OAI

/-! A compact ambient family retains any prescribed strict modulus
threshold. This is the tightness localization for the Borel-image argument. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_modulus_localization
    {A Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z)
    {c : ℝ≥0∞} (hc : c < measureFamilyModulus A Z σ K) :
    ∃ T : Set (FiniteMeasure Z), IsCompact T ∧
      c < measureFamilyModulus {a | K a ∈ T} Z σ (fun a => K a.val) := by
  have hr := ENNReal.rpow_lt_rpow hc (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨δ,hδ,hδlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hr
  have he : (0 : ℝ≥0∞) < (δ : ℝ≥0∞)^2 := by positivity
  obtain ⟨T,h,hT,hh,henergy,hcontrol⟩ := exists_compact_finiteMeasure_control σ he
  refine ⟨T,hT,?_⟩
  let S : Set A := {a | K a ∈ T}
  have hbad : measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val) < (δ : ℝ≥0∞)^2 := by
    exact (measureFamilyModulus_le_admissible σ (fun a : (Sᶜ : Set A) => K a.val) hh
      (fun a => hcontrol (K a.val) a.property)).trans_lt henergy
  have hbadroot : (measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val)) ^ (1/2 : ℝ) ≤ δ := by
    have hb := ENNReal.rpow_le_rpow hbad.le (by norm_num : (0 : ℝ) ≤ 1/2)
    simpa only [← ENNReal.rpow_two,← ENNReal.rpow_mul,
      show (2 : ℝ)*(1/2)=1 by norm_num,ENNReal.rpow_one] using hb
  by_contra hn
  have hgood : measureFamilyModulus S Z σ (fun a => K a.val) ≤ c := le_of_not_gt hn
  have hsplit := measureFamilyModulus_sqrt_subadditive σ K S Sᶜ (union_compl_self S)
  have hbound : (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤ c ^ (1/2 : ℝ) + δ :=
    hsplit.trans (add_le_add (ENNReal.rpow_le_rpow hgood (by norm_num)) hbadroot)
  exact (not_lt_of_ge hbound) hδlt

end CircleDomainRigidity

end

end OAI
