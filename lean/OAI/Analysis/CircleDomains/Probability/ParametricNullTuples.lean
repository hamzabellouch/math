import OAI.Analysis.CircleDomains.Probability.NullLevelTuples

namespace OAI

/-! Borel scalar-level envelopes remain Borel after forming finite tuples
and active slots, also when they depend on an earlier sampled path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω : Type*} [MeasurableSpace Ω]

def badTupleGraph (N : Ω → ℕ → Set UnitAddCircle) : Set (Ω × LevelTuple) :=
  {q | q.2 ∈ tuplesWithBadLevel (N q.1)}

theorem measurableSet_badTupleGraph (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i}) :
    MeasurableSet (badTupleGraph N) := by
  let f (i : TupleType) : Ω × (Fin (i.1 + 1) → UnitAddCircle) → Ω × LevelTuple :=
    Prod.map id (tupleFiber i)
  have he : badTupleGraph N = ⋃ i : TupleType, f i '' (f i ⁻¹' badTupleGraph N) := by
    ext q
    constructor
    · intro hq
      rcases q with ⟨ω, n, l, t⟩
      exact mem_iUnion.mpr ⟨⟨n, l⟩, (ω, t), hq, rfl⟩
    · intro h
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp h
      exact hp
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  apply (MeasurableEmbedding.id.prodMap (measurableEmbedding_tupleFiber i)).measurableSet_image.mpr
  change MeasurableSet {q : Ω × (Fin (i.1 + 1) → UnitAddCircle) |
    ∃ j, q.2 j ∈ N q.1 (i.2 j)}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun j => (hN (i.2 j)).preimage
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

def badSlotGraph (N : Ω → ℕ → Set UnitAddCircle) : Set (Ω × TagSlot) :=
  {p | ∃ q, p.2 = Sum.inr q ∧ tagDataTuple q ∈ tuplesWithBadLevel (N p.1)}

theorem measurableSet_badSlotGraph (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i}) :
    MeasurableSet (badSlotGraph N) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have he : badSlotGraph N = Prod.map id activeTagSlot ''
      (Prod.map id tagDataTuple ⁻¹' badTupleGraph N) := by
    ext p
    constructor
    · rintro ⟨q, hq, hmem⟩
      exact ⟨(p.1, q), hmem, Prod.ext rfl hq.symm⟩
    · rintro ⟨⟨ω, q⟩, hq, rfl⟩
      exact ⟨q, rfl, hq⟩
  rw [he]
  have hi : Topology.IsOpenEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  apply (MeasurableEmbedding.id.prodMap hme).measurableSet_image.mpr
  exact (measurableSet_badTupleGraph N hN).preimage
    (measurable_id.prodMap continuous_tagDataTuple.measurable)

end CircleDomainRigidity

end

end OAI
