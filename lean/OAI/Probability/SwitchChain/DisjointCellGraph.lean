import OAI.Probability.SwitchChain.DisjointBlockGraph
import OAI.Probability.SwitchChain.PairArrayEncoding

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointBlock
variable {O : Type*} [Fintype O]

def cellData (H : SimpleGraph O) (a b : Bool) (ca cb : O → ℕ)
    (M : Fin 2 → Fin 2 → Bool) (A B : Finset O) : Data O :=
  ⟨H, a, b, M, outsideArray ca A, outsideArray cb B⟩

def cellGraph (H : SimpleGraph O) (a b : Bool) (ca cb : O → ℕ)
    (M : Fin 2 → Fin 2 → Bool) (A B : Finset O) : SimpleGraph (Vertex O) :=
  graph (cellData H a b ca cb M A B)

 theorem cellData_encode (D : Data O) :
    cellData D.outside D.internalA D.internalB (pairCount D.outsideA)
      (pairCount D.outsideB) D.cross (assignmentSet D.outsideA)
      (assignmentSet D.outsideB) = D := by
  simp only [cellData, outsideArray_encode]

 theorem cellGraph_encode (G : SimpleGraph (Vertex O)) :
    cellGraph (encode G).outside (encode G).internalA (encode G).internalB
      (pairCount (encode G).outsideA) (pairCount (encode G).outsideB)
      (encode G).cross (assignmentSet (encode G).outsideA)
      (assignmentSet (encode G).outsideB) = G := by
  rw [cellGraph, cellData_encode, graph_encode]

 theorem valence_cellGraph_outside (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (hca : ∀ o, ca o ≤ 2) (hcb : ∀ o, cb o ≤ 2)
    (M : Fin 2 → Fin 2 → Bool) (A B : Finset O)
    (hA : A ⊆ singleSet ca) (hB : B ⊆ singleSet cb) (o : O) :
    valence (cellGraph H a b ca cb M A B) (Sum.inr (Sum.inr o)) =
      valence H o + ca o + cb o := by
  rw [cellGraph, valence_graph_outside]
  change valence H o + (∑ i, (outsideArray ca A i o).toNat) +
    (∑ j, (outsideArray cb B j o).toNat) = _
  simp only [Fin.sum_univ_two]
  change valence H o + pairCount (outsideArray ca A) o + pairCount (outsideArray cb B) o = _
  rw [pairCount_outsideArray ca hca A hA, pairCount_outsideArray cb hcb B hB]

 theorem valence_cellGraph_A_zero (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (M : Fin 2 → Fin 2 → Bool) (A B : Finset O)
    (hA : A ⊆ singleSet ca) :
    valence (cellGraph H a b ca cb M A B) (Sum.inl 0) =
      a.toNat + (∑ j, (M 0 j).toNat) + (doubleSet ca).card + A.card := by
  rw [cellGraph, valence_graph_A]
  change a.toNat + (∑ j, (M 0 j).toNat) + (∑ o, (outsideArray ca A 0 o).toNat) = _
  rw [outsideArray_first_sum ca A hA]
  omega

 theorem valence_cellGraph_A_one [DecidableEq O] (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (M : Fin 2 → Fin 2 → Bool) (A B : Finset O) :
    valence (cellGraph H a b ca cb M A B) (Sum.inl 1) =
      a.toNat + (∑ j, (M 1 j).toNat) + (doubleSet ca).card + (singleSet ca \ A).card := by
  rw [cellGraph, valence_graph_A]
  change a.toNat + (∑ j, (M 1 j).toNat) + (∑ o, (outsideArray ca A 1 o).toNat) = _
  rw [outsideArray_second_sum]
  omega

 theorem valence_cellGraph_B_zero (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (M : Fin 2 → Fin 2 → Bool) (A B : Finset O)
    (hB : B ⊆ singleSet cb) :
    valence (cellGraph H a b ca cb M A B) (Sum.inr (Sum.inl 0)) =
      b.toNat + (∑ i, (M i 0).toNat) + (doubleSet cb).card + B.card := by
  rw [cellGraph, valence_graph_B]
  change b.toNat + (∑ i, (M i 0).toNat) + (∑ o, (outsideArray cb B 0 o).toNat) = _
  rw [outsideArray_first_sum cb B hB]
  omega

 theorem valence_cellGraph_B_one [DecidableEq O] (H : SimpleGraph O) (a b : Bool)
    (ca cb : O → ℕ) (M : Fin 2 → Fin 2 → Bool) (A B : Finset O) :
    valence (cellGraph H a b ca cb M A B) (Sum.inr (Sum.inl 1)) =
      b.toNat + (∑ i, (M i 1).toNat) + (doubleSet cb).card + (singleSet cb \ B).card := by
  rw [cellGraph, valence_graph_B]
  change b.toNat + (∑ i, (M i 1).toNat) + (∑ o, (outsideArray cb B 1 o).toNat) = _
  rw [outsideArray_second_sum]
  omega

structure InCell (H : SimpleGraph O) (a b : Bool) (ca cb : O → ℕ)
    (G : SimpleGraph (Vertex O)) : Prop where
  outside : (encode G).outside = H
  internalA : (encode G).internalA = a
  internalB : (encode G).internalB = b
  countA : pairCount (encode G).outsideA = ca
  countB : pairCount (encode G).outsideB = cb

 theorem cellGraph_mem (H : SimpleGraph O) (a b : Bool) (ca cb : O → ℕ)
    (hca : ∀ o, ca o ≤ 2) (hcb : ∀ o, cb o ≤ 2)
    (M : Fin 2 → Fin 2 → Bool) (A B : Finset O)
    (hA : A ⊆ singleSet ca) (hB : B ⊆ singleSet cb) :
    InCell H a b ca cb (cellGraph H a b ca cb M A B) := by
  constructor
  · simp only [cellGraph, encode_graph, cellData]
  · simp only [cellGraph, encode_graph, cellData]
  · simp only [cellGraph, encode_graph, cellData]
  · simp only [cellGraph, encode_graph, cellData]
    exact funext (pairCount_outsideArray ca hca A hA)
  · simp only [cellGraph, encode_graph, cellData]
    exact funext (pairCount_outsideArray cb hcb B hB)

def cellEquiv (H : SimpleGraph O) (a b : Bool) (ca cb : O → ℕ)
    (hca : ∀ o, ca o ≤ 2) (hcb : ∀ o, cb o ≤ 2) :
    {G : SimpleGraph (Vertex O) // InCell H a b ca cb G} ≃
      (Fin 2 → Fin 2 → Bool) ×
        {A : Finset O // A ⊆ singleSet ca} × {B : Finset O // B ⊆ singleSet cb} where
  toFun G := ((encode G.val).cross,
    ⟨assignmentSet (encode G.val).outsideA, by
      have h := assignmentSet_subset (encode G.val).outsideA
      simpa only [singleSet, G.property.countA] using h⟩,
    ⟨assignmentSet (encode G.val).outsideB, by
      have h := assignmentSet_subset (encode G.val).outsideB
      simpa only [singleSet, G.property.countB] using h⟩)
  invFun z := ⟨cellGraph H a b ca cb z.1 z.2.1.val z.2.2.val,
    cellGraph_mem H a b ca cb hca hcb z.1 z.2.1.val z.2.2.val
      z.2.1.property z.2.2.property⟩
  left_inv G := by
    apply Subtype.ext
    have h := cellGraph_encode G.val
    rw [G.property.outside, G.property.internalA, G.property.internalB,
      G.property.countA, G.property.countB] at h
    exact h
  right_inv z := by
    rcases z with ⟨M, A, B⟩
    apply Prod.ext
    · simp only [cellGraph, encode_graph, cellData]
    · apply Prod.ext <;> apply Subtype.ext
      · simpa only [cellGraph, encode_graph, cellData] using
          assignmentSet_outsideArray ca hca A.val A.property
      · simpa only [cellGraph, encode_graph, cellData] using
          assignmentSet_outsideArray cb hcb B.val B.property

end Problem315.DisjointBlock

end

end OAI
