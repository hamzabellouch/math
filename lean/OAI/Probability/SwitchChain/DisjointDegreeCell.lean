import OAI.Probability.SwitchChain.DisjointCellGraph

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointBlock
variable {O : Type*} [Fintype O] [DecidableEq O]

structure Feasible (d : Vertex O → ℕ) (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (M : Fin 2 → Fin 2 → Bool) (A B : Finset O) : Prop where
  firstZero : a.toNat + (∑ j, (M 0 j).toNat) + (doubleSet ca).card + A.card = d (Sum.inl 0)
  firstOne : a.toNat + (∑ j, (M 1 j).toNat) + (doubleSet ca).card +
    (singleSet ca \ A).card = d (Sum.inl 1)
  secondZero : b.toNat + (∑ i, (M i 0).toNat) + (doubleSet cb).card + B.card =
    d (Sum.inr (Sum.inl 0))
  secondOne : b.toNat + (∑ i, (M i 1).toNat) + (doubleSet cb).card +
    (singleSet cb \ B).card = d (Sum.inr (Sum.inl 1))
  outside : ∀ o, valence H o + ca o + cb o = d (Sum.inr (Sum.inr o))

 theorem cellGraph_valences_iff (d : Vertex O → ℕ) (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (hca : ∀ o, ca o ≤ 2) (hcb : ∀ o, cb o ≤ 2)
    (M : Fin 2 → Fin 2 → Bool) (A B : Finset O)
    (hA : A ⊆ singleSet ca) (hB : B ⊆ singleSet cb) :
    (∀ v, valence (cellGraph H a b ca cb M A B) v = d v) ↔
      Feasible d H a b ca cb M A B := by
  constructor
  · intro h
    constructor
    · simpa only [valence_cellGraph_A_zero H a b ca cb M A B hA] using h (Sum.inl 0)
    · simpa only [valence_cellGraph_A_one] using h (Sum.inl 1)
    · simpa only [valence_cellGraph_B_zero H a b ca cb M A B hB] using h (Sum.inr (Sum.inl 0))
    · simpa only [valence_cellGraph_B_one] using h (Sum.inr (Sum.inl 1))
    · intro o
      simpa only [valence_cellGraph_outside H a b ca cb hca hcb M A B hA hB] using
        h (Sum.inr (Sum.inr o))
  · intro h v
    rcases v with i | j | o
    · fin_cases i
      · exact (valence_cellGraph_A_zero H a b ca cb M A B hA).trans h.firstZero
      · exact (valence_cellGraph_A_one H a b ca cb M A B).trans h.firstOne
    · fin_cases j
      · exact (valence_cellGraph_B_zero H a b ca cb M A B hB).trans h.secondZero
      · exact (valence_cellGraph_B_one H a b ca cb M A B).trans h.secondOne
    · rw [valence_cellGraph_outside H a b ca cb hca hcb M A B hA hB]
      exact h.outside o

def degreeCellEquiv (d : Vertex O → ℕ) (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (hca : ∀ o, ca o ≤ 2) (hcb : ∀ o, cb o ≤ 2) :
    {G : {G : SimpleGraph (Vertex O) // InCell H a b ca cb G} //
      ∀ v, valence G.val v = d v} ≃
    {z : (Fin 2 → Fin 2 → Bool) ×
      {A : Finset O // A ⊆ singleSet ca} × {B : Finset O // B ⊆ singleSet cb} //
      Feasible d H a b ca cb z.1 z.2.1.val z.2.2.val} :=
  (cellEquiv H a b ca cb hca hcb).subtypeEquiv (by
    intro G
    have hA : assignmentSet (encode G.val).outsideA ⊆ singleSet ca := by
      simpa only [singleSet, G.property.countA] using
        assignmentSet_subset (encode G.val).outsideA
    have hB : assignmentSet (encode G.val).outsideB ⊆ singleSet cb := by
      simpa only [singleSet, G.property.countB] using
        assignmentSet_subset (encode G.val).outsideB
    have hreconstruct := cellGraph_encode G.val
    rw [G.property.outside, G.property.internalA, G.property.internalB,
      G.property.countA, G.property.countB] at hreconstruct
    have h := cellGraph_valences_iff d H a b ca cb hca hcb (encode G.val).cross
      (assignmentSet (encode G.val).outsideA) (assignmentSet (encode G.val).outsideB) hA hB
    rw [hreconstruct] at h
    exact h)

end Problem315.DisjointBlock

end

end OAI
