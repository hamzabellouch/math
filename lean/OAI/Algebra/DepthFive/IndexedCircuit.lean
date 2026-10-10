import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section

namespace Problem335

/-- A depth-five circuit whose gates are indexed by arbitrary finite types.
This representation is convenient for products, sums, and path-indexed gates;
`toDepth5Circuit` transports it to the qualified circuit representation. -/
structure IndexedDepth5Circuit (K : Type*) [CommSemiring K] (n : ℕ)
    (L B P M U : Type*) where
  leaves : L → D5Leaf K n
  bottomInputs : B → List (K × L)
  bottomDegree : B → ℕ
  bottomHomogeneous :
    ∀ i entry, entry ∈ bottomInputs i → d5LeafDegree (leaves entry.2) = bottomDegree i
  bottomEmpty :
    ∀ i, bottomInputs i = [] → bottomDegree i = 0
  lowerInputs : P → List B
  middleInputs : M → List (K × P)
  middleDegree : M → ℕ
  middleHomogeneous :
    ∀ i entry, entry ∈ middleInputs i →
      ((lowerInputs entry.2).map bottomDegree).sum = middleDegree i
  middleEmpty :
    ∀ i, middleInputs i = [] → middleDegree i = 0
  upperInputs : U → List M
  outputInputs : List (K × U)
  outputDegree : ℕ
  outputHomogeneous :
    ∀ entry, entry ∈ outputInputs →
      ((upperInputs entry.2).map middleDegree).sum = outputDegree
  outputEmpty : outputInputs = [] → outputDegree = 0

namespace IndexedDepth5Circuit

variable {K : Type*} [CommSemiring K] {n : ℕ}
variable {L B P M U : Type*}
variable [Fintype L] [Fintype B] [Fintype P] [Fintype M] [Fintype U]

/-- Relabel each finite gate type by `Fin` without changing any wire or degree. -/
def toDepth5Circuit (c : IndexedDepth5Circuit K n L B P M U) : Depth5Circuit K n where
  leafCount := Fintype.card L
  leaves i := c.leaves ((Fintype.equivFin L).symm i)
  bottomCount := Fintype.card B
  bottomInputs i := (c.bottomInputs ((Fintype.equivFin B).symm i)).map
    (fun e => (e.1, Fintype.equivFin L e.2))
  bottomDegree i := c.bottomDegree ((Fintype.equivFin B).symm i)
  bottomHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa using c.bottomHomogeneous ((Fintype.equivFin B).symm i) e he
  bottomEmpty := by
    intro i h
    exact c.bottomEmpty _ (List.map_eq_nil_iff.mp h)
  lowerCount := Fintype.card P
  lowerInputs i := (c.lowerInputs ((Fintype.equivFin P).symm i)).map (Fintype.equivFin B)
  middleCount := Fintype.card M
  middleInputs i := (c.middleInputs ((Fintype.equivFin M).symm i)).map
    (fun e => (e.1, Fintype.equivFin P e.2))
  middleDegree i := c.middleDegree ((Fintype.equivFin M).symm i)
  middleHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa [List.map_map, Function.comp_def] using
      c.middleHomogeneous ((Fintype.equivFin M).symm i) e he
  middleEmpty := by
    intro i h
    exact c.middleEmpty _ (List.map_eq_nil_iff.mp h)
  upperCount := Fintype.card U
  upperInputs i := (c.upperInputs ((Fintype.equivFin U).symm i)).map (Fintype.equivFin M)
  outputInputs := c.outputInputs.map (fun e => (e.1, Fintype.equivFin U e.2))
  outputDegree := c.outputDegree
  outputHomogeneous := by
    intro entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa [List.map_map, Function.comp_def] using c.outputHomogeneous e he
  outputEmpty := by
    intro h
    exact c.outputEmpty (List.map_eq_nil_iff.mp h)

@[simp] theorem circuitSize_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    circuitSize c.toDepth5Circuit =
      Fintype.card L + Fintype.card B + Fintype.card P +
        Fintype.card M + Fintype.card U + 1 := rfl

@[simp] theorem outputDegree_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    c.toDepth5Circuit.outputDegree = c.outputDegree := rfl

end IndexedDepth5Circuit
end Problem335

end

end OAI
