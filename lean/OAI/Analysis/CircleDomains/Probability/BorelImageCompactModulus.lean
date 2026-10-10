import OAI.Analysis.CircleDomains.Modulus.CompactContinuousImageModulus
import OAI.Analysis.CircleDomains.Probability.PositiveMassCompactLocalization
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Compact inner approximation for the pointwise modulus of a Borel image.
The compatible Polish topology is refined only after compact localization. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_subfamily_of_borel_image
    {A Z : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z) (hKm : Measurable K)
    (hK : ∀ a, K a ≠ 0) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ K) :
    ∃ S : Set (FiniteMeasure Z), IsCompact S ∧ S ⊆ range K ∧
      c < measureFamilyModulus S Z σ (fun v => v.val) := by
  classical
  obtain ⟨T,hT,hTz,hmod⟩ := exists_compact_nonzero_modulus_localization σ K hK hc
  let B : Set A := {a | K a ∈ T}
  have hBm : MeasurableSet B := hKm (compact_finiteMeasure_measurableSet hT)
  let : StandardBorelSpace B := hBm.standardBorel
  let := upgradeStandardBorel B
  let : BorelSpace T := compact_finiteMeasure_borel hT
  let : PolishSpace T := compact_finiteMeasure_polish hT
  let f : B → T := fun a => ⟨K a.val,a.property⟩
  have hfm : Measurable f := (hKm.comp measurable_subtype_coe).subtype_mk
  obtain ⟨t,hle,hfc,ht⟩ := hfm.exists_continuous
  have hbe : @BorelSpace B t inferInstance := by
    constructor
    rw [eq_borel_upgradeStandardBorel B,borel_eq_borel_of_le ht _ hle]
    infer_instance
  let : TopologicalSpace B := t
  let : PolishSpace B := ht
  let : BorelSpace B := hbe
  let := upgradeIsCompletelyMetrizable B
  cases isEmpty_or_nonempty B with
  | inl hB =>
    have hz := measureFamilyModulus_zero_of_isEmpty σ (fun a : B => K a.val)
    rw [hz] at hmod
    exact (not_lt_of_ge bot_le hmod).elim
  | inr hB =>
    obtain ⟨S,hS,hSf,hSc⟩ := exists_compact_subfamily_of_continuous_image σ hT hTz f hfc hmod
    refine ⟨S,hS,?_,hSc⟩
    rintro v hv
    obtain ⟨a,ha⟩ := hSf hv
    exact ⟨a.val,ha⟩

end CircleDomainRigidity

end

end OAI
