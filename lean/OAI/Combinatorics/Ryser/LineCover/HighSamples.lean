import OAI.Combinatorics.Ryser.LineCover.Definitions
import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins
import Mathlib.Data.Fintype.CardEmbedding

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

abbrev PencilPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(coverPencil L p)

abbrev ComplementPopulation (L : Finset (AffineLine F)) (p : ProjectivePoint F) :=
  ↥(L \ coverPencil L p)

abbrev HighSample (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ) :=
  (Fin t ↪ PencilPopulation L p) × (Fin t ↪ ComplementPopulation L p)

theorem pencilPopulation_incident (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) : ProjectiveIncidence p (some k.val) :=
  (mem_coverPencil L p k.val).mp k.property |>.2

theorem complementPopulation_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) : c.val ∈ L := let _ := instFintypeF;
  (Finset.mem_sdiff.mp c.property).1

theorem complementPopulation_not_incident (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (c : ComplementPopulation L p) :
    ¬ ProjectiveIncidence p (some c.val) := by
  intro hc
  exact (Finset.mem_sdiff.mp c.property).2
    ((mem_coverPencil L p c.val).mpr ⟨complementPopulation_mem L p c, hc⟩)

theorem pencil_ne_complement (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (k : PencilPopulation L p) (c : ComplementPopulation L p) : k.val ≠ c.val := by
  intro h
  apply complementPopulation_not_incident L p c
  rw [← h]
  exact pencilPopulation_incident L p k

def highTuple (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    (s : HighSample L p t) : LineTuple F t where
  toFun := Sum.elim (fun i => (s.1 i).val) (fun j => (s.2 j).val)
  inj' := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (s.1.injective (Subtype.ext hab))
      | inr j => exact (pencil_ne_complement L p (s.1 i) (s.2 j) hab).elim
    | inr i =>
      cases b with
      | inl j => exact (pencil_ne_complement L p (s.1 j) (s.2 i) hab.symm).elim
      | inr j => exact congrArg Sum.inr (s.2.injective (Subtype.ext hab))

@[simp] theorem highTuple_left (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inl i) = (s.1 i).val := rfl

@[simp] theorem highTuple_right (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t) :
    highTuple L p s (Sum.inr i) = (s.2 i).val := rfl

theorem highTuple_mem (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} (s : HighSample L p t) (i : Fin t ⊕ Fin t) : highTuple L p s i ∈ L := by
  cases i with
  | inl i => exact coverPencil_subset L p (s.1 i).property
  | inr i => exact complementPopulation_mem L p (s.2 i)

def highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  Finset.univ.filter fun kc =>
    ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val

@[simp] theorem mem_highCrossPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highCrossPairs X L p ↔
      ∃ x ∈ X, Incidence x kc.1.val ∧ Incidence x kc.2.val := let _ := instFintypeF; by
  simp only [highCrossPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : Finset (PencilPopulation L p × ComplementPopulation L p) :=
  (highCrossPairs S L p).filter fun kc =>
    S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val

@[simp] theorem mem_highShapePairs (S : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (kc : PencilPopulation L p × ComplementPopulation L p) :
    kc ∈ highShapePairs S L p ↔
      (∃ x ∈ S, Incidence x kc.1.val ∧ Incidence x kc.2.val) ∧
      S ≠ linePoints kc.1.val ∧ S ≠ linePoints kc.2.val := by
  simp only [highShapePairs, Finset.mem_filter, mem_highCrossPairs]

def highSurvivorPairCount (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) {t : ℕ} (s : HighSample L p t) : ℕ :=
  (Finset.univ.filter fun ij : Fin t × Fin t =>
    (s.1 ij.1, s.2 ij.2) ∈ highCrossPairs X L p).card

end RyserCoveringCounterexample.LineCover

end

end OAI
