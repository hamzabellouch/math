import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayClosed

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def selectedOffsets {d : ℕ} (e : Direction d)
    (u : ℕ → StationaryCompact.Label) (Y : ActualEpisodeArray e) :
    ReferenceClasses.Offsets (HorizontalSpace e) := fun p => Y.2.1 (u p.1,u p.2)

def ArrayOffsetsConsistent {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ u : ℕ → StationaryCompact.Label, ReferenceClasses.Consistent (selectedOffsets e u Y)

lemma arrayOffsetsConsistent_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayOffsetsConsistent e Y} := by
  unfold ArrayOffsetsConsistent
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun u => ReferenceClasses.consistent_closed.preimage
    (by unfold selectedOffsets; fun_prop)

lemma actual_arrayOffsetsConsistent {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    ArrayOffsetsConsistent e (actualArrayMap e t J X) := by
  intro u
  constructor
  · intro a
    simp [selectedOffsets,actualArrayMap]
  · intro a b z h
    have he : X.1.2 (u b)-X.1.2 (u a)=z := OnePoint.coe_injective h
    change ((X.1.2 (u a)-X.1.2 (u b) : HorizontalSpace e):OnePoint (HorizontalSpace e))=
      ((-z : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←he,neg_sub]
  · intro a b c z w h₁ h₂
    have h₁ : X.1.2 (u b)-X.1.2 (u a)=z := OnePoint.coe_injective h₁
    have h₂ : X.1.2 (u c)-X.1.2 (u b)=w := OnePoint.coe_injective h₂
    change ((X.1.2 (u c)-X.1.2 (u a) : HorizontalSpace e):OnePoint (HorizontalSpace e))=
      ((z+w : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←h₁,←h₂]
    congr 1
    abel

lemma arrayOffsetsConsistent_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) : ArrayOffsetsConsistent e (StationaryCompact.shift Y) := by
  intro u
  exact h (fun n => ((u n).1+1,(u n).2))

lemma actualOccupation_offsetsConsistent {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ArrayOffsetsConsistent e Y :=
  actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (arrayOffsetsConsistent_closed e).measurableSet (actual_arrayOffsetsConsistent e t J)
    (arrayOffsetsConsistent_shift e)

noncomputable def allLabelData {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) : ReferenceClasses.Data (HorizontalSpace e) :=
  ⟨selectedOffsets e (Denumerable.eqv StationaryCompact.Label).symm Y,
    h (Denumerable.eqv StationaryCompact.Label).symm⟩

end DirectionalTransience

end

end OAI
