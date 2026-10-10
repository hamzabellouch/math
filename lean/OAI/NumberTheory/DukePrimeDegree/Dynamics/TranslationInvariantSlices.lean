import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! # Haar slices of a measure invariant in its second coordinate

Only relatively compact transverse sets are needed for local product charts.
The transverse measure itself is allowed to be singular.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

def secondCoordinateSlice (ρ : Measure (Z × V)) (A : Set Z) : Measure V :=
  (ρ.restrict (A ×ˢ univ)).map Prod.snd

lemma secondCoordinateSlice_apply (ρ : Measure (Z × V)) (A : Set Z)
    {B : Set V} (hB : MeasurableSet B) :
    secondCoordinateSlice ρ A B=ρ (A ×ˢ B) := by
  rw [secondCoordinateSlice,Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,and_true]
  exact and_comm

theorem secondCoordinateSlice_invariant [Add V] [MeasurableAdd₂ V]
    (ρ : Measure (Z × V)) (A : Set Z) (hA : MeasurableSet A)
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ) :
    Measure.IsAddLeftInvariant (secondCoordinateSlice ρ A) := by
  constructor
  intro v
  ext B hB
  have hm : Measurable (fun w : V => v+w) := measurable_const.add measurable_id
  have hM : Measurable (fun z : Z × V => (z.1,v+z.2)) :=
    measurable_fst.prodMk (measurable_const.add measurable_snd)
  rw [Measure.map_apply hm hB,secondCoordinateSlice_apply ρ A (hB.preimage hm),
    secondCoordinateSlice_apply ρ A hB]
  have he : A ×ˢ ((fun w : V => v+w) ⁻¹' B)=
      (fun z : Z × V => (z.1,v+z.2)) ⁻¹' (A ×ˢ B) := rfl
  rw [he,←Measure.map_apply hM (hA.prod hB),hinv]

variable [TopologicalSpace Z] [TopologicalSpace V] [BorelSpace Z] [BorelSpace V]
  [T2Space V]

omit [BorelSpace Z] in
theorem secondCoordinateSlice_finiteOnCompacts (ρ : Measure (Z × V))
    [IsFiniteMeasureOnCompacts ρ] {A : Set Z} (hA : IsCompact (closure A)) :
    IsFiniteMeasureOnCompacts (secondCoordinateSlice ρ A) := by
  constructor
  intro B hB
  rw [secondCoordinateSlice_apply ρ A hB.measurableSet]
  exact (measure_mono (Set.prod_mono subset_closure Subset.rfl)).trans_lt
    (hA.prod hB).measure_lt_top

omit [BorelSpace Z] in
theorem secondCoordinateSlice_eq_haar [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    {A : Set Z} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, secondCoordinateSlice ρ A=c • η := by
  let := secondCoordinateSlice_finiteOnCompacts ρ hAc
  let := secondCoordinateSlice_invariant ρ A hA hinv
  exact ⟨_,Measure.isAddLeftInvariant_eq_smul _ _⟩

omit [BorelSpace Z] in
theorem translationInvariant_rectangle [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    {A : Set Z} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, ∀ B : Set V, MeasurableSet B →
      ρ (A ×ˢ B)=(c : ℝ≥0∞)*η B := by
  obtain ⟨c,hc⟩ := secondCoordinateSlice_eq_haar ρ hA hAc hinv η
  refine ⟨c,fun B hB => ?_⟩
  rw [←secondCoordinateSlice_apply ρ A hB,hc,Measure.smul_apply]
  rfl

end DukePrimeDegree

end

end OAI
