import OAI.Analysis.CircleDomains.Selection.TagContainment

namespace OAI

/-! Borel tests for nonconstant active tags and excluded level tuples. -/

open Set MeasureTheory Topology
open scoped Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def nonconstantTagSegment : Set (C(PathTime, X) × TagSlot) :=
  {q | ∃ s t : PathTime,
    tagLeft q.2 < s ∧ s < tagRight q.2 ∧
    tagLeft q.2 < t ∧ t < tagRight q.2 ∧ q.1 s ≠ q.1 t}

theorem isOpen_nonconstantTagSegment : IsOpen (nonconstantTagSegment (X := X)) := by
  simp only [nonconstantTagSegment, ofPred_exists]
  apply isOpen_iUnion
  intro s
  apply isOpen_iUnion
  intro t
  have hl : Continuous (fun q : C(PathTime, X) × TagSlot => (tagLeft q.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_tagLeft.comp continuous_snd)
  have hr : Continuous (fun q : C(PathTime, X) × TagSlot => (tagRight q.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_tagRight.comp continuous_snd)
  exact (isOpen_lt hl continuous_const).inter
    ((isOpen_lt continuous_const hr).inter
      ((isOpen_lt hl continuous_const).inter
        ((isOpen_lt continuous_const hr).inter
          (isClosed_eq ((continuous_eval_const s).comp continuous_fst)
            ((continuous_eval_const t).comp continuous_fst)).isOpen_compl)))

def validTagShape : Set (C(PathTime, X) × TagSlot) :=
  (Prod.snd ⁻¹' Set.range (Sum.inl : Unit → TagSlot)) ∪ nonconstantTagSegment

theorem isOpen_validTagShape : IsOpen (validTagShape (X := X)) :=
  (isOpen_range_inl.preimage continuous_snd).union isOpen_nonconstantTagSegment

def insertTagTuple (n : ℕ) (l : Fin (n + 1) → ℕ)
    (p : (Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) : TagSlot :=
  Sum.inr ⟨n, l, p⟩

theorem isClosedEmbedding_insertTagTuple (n : ℕ) (l : Fin (n + 1) → ℕ) :
    IsClosedEmbedding (insertTagTuple n l) := by
  have hp : IsClosedEmbedding
      (Prod.mk l : ((Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) → TagParameters n) := by
    refine ⟨isEmbedding_prodMkRight l, ?_⟩
    have heq : Set.range
        (Prod.mk l : ((Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) → TagParameters n) =
        {p | p.1 = l} := by
      ext p
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · intro h
        exact ⟨p.2, Prod.ext h.symm rfl⟩
    rw [heq]
    exact isClosed_eq continuous_fst continuous_const
  exact IsClosedEmbedding.inr.comp (IsClosedEmbedding.sigmaMk.comp hp)

def tagTupleExcluded (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)) :
    Set TagSlot :=
  ⋃ n, ⋃ l, insertTagTuple n l '' (N n l ×ˢ (univ : Set (PathTime × PathTime)))

theorem measurableSet_tagTupleExcluded
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) : MeasurableSet (tagTupleExcluded N) := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro l
  exact (isClosedEmbedding_insertTagTuple n l).measurableEmbedding.measurableSet_image.mpr
    ((hN n l).prod MeasurableSet.univ)

end CircleDomainRigidity

end

end OAI
