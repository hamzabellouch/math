import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Local.ReuseExtensionTable

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => T.generator i ∈ old)

omit [Field F] [Fintype F] in
theorem image_oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F)) :
    (oldGeneratorIndices T old).image T.generator = generatorSet T ∩ old := by
  ext d
  simp only [oldGeneratorIndices, generatorSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩
    exact ⟨i, hi, rfl⟩

omit [Field F] [Fintype F] in
theorem card_oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F))
    (hT : Function.Injective T.generator) :
    (oldGeneratorIndices T old).card = (generatorSet T ∩ old).card := by
  rw [← image_oldGeneratorIndices, Finset.card_image_of_injective _ hT]

omit [Fintype F] in

theorem tuplePoint_eq_of_fixedGeneratorPosition (M N : MergedPairs F) (T : FourTuple F)
    (old : Finset (Direction F))
    (hMN : ∀ d ∈ old, ∀ b, M d b = N d b) (i : Fin 4)
    (hi : i ∈ fixedGeneratorPositions (oldGeneratorIndices T old)) :
    tuplePoint M T i = tuplePoint N T i := by
  obtain ⟨hi, hinext⟩ := Finset.mem_filter.mp hi
  have hi' : T.generator i ∈ old := (Finset.mem_filter.mp hi).2
  have hinext' : T.generator (i + 1) ∈ old := (Finset.mem_filter.mp hinext).2
  simp only [tuplePoint, constituent, hMN _ hi', hMN _ hinext']

omit [Field F] [Fintype F] in

theorem fixedTuplePositions_table (T : FourTuple F) (old : Finset (Direction F))
    (hT : Function.Injective T.generator) :
    let j := (generatorSet T ∩ old).card
    let f := (fixedGeneratorPositions (oldGeneratorIndices T old)).card
    (j = 0 → f = 0) ∧ (j = 1 → f = 0) ∧ (j = 2 → f ≤ 1) ∧
      (j = 3 → f ≤ 2) ∧ (j = 4 → f = 4) := by
  simpa only [card_oldGeneratorIndices T old hT] using
    fixedGeneratorPositions_table (oldGeneratorIndices T old)

omit [Field F] [Fintype F] in
theorem tuple_reuseSaving_le_countingExponent (T : FourTuple F)
    (old : Finset (Direction F)) (hT : Function.Injective T.generator) :
    reuseSaving (generatorSet T ∩ old).card ≤
      reuseCountingExponent (oldGeneratorIndices T old) := by
  simpa only [card_oldGeneratorIndices T old hT] using
    reuseSaving_le_countingExponent (oldGeneratorIndices T old)

theorem Configuration.exists_six_tuple_reuse_order (C : Configuration F)
    (hvalid : C.Valid) (hcompatible : C.Compatible) (s : Finset (Slot F))
    (hreuse : 3 ≤ 4 * s.card -
      (s.biUnion (fun i => generatorSet (C.choice i).tuple)).card) :
    ∃ l : List (Slot F), l.Nodup ∧ l.toFinset ⊆ s ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore (fun i => generatorSet (C.choice i).tuple) l := by
  apply Balanced.exists_six_tuple_reuse_order _ s ?_ ?_ hreuse
  · intro i _hi
    rw [generatorSet, Finset.card_image_of_injective _ (hvalid.2 i).2.2.1]
    simp
  · intro i _hi j _hj hij
    exact hcompatible.2.1 i j hij

end
end Balanced

end OAI
