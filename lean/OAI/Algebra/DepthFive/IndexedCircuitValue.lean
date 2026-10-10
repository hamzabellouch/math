import OAI.Algebra.DepthFive.IndexedCircuit

namespace OAI

noncomputable section

namespace Problem335
namespace IndexedDepth5Circuit

variable {K : Type*} [CommSemiring K] {n : ℕ}
variable {L B P M U : Type*}

/-- Value of a bottom gate before relabelling the gate types. -/
def bottomValue (c : IndexedDepth5Circuit K n L B P M U) (i : B) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.bottomInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * d5LeafValue (c.leaves entry.2))).sum

/-- Value of a lower product gate before relabelling the gate types. -/
def lowerValue (c : IndexedDepth5Circuit K n L B P M U) (i : P) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.lowerInputs i).map (fun j => bottomValue c j)).prod

/-- Value of a middle sum gate before relabelling the gate types. -/
def middleValue (c : IndexedDepth5Circuit K n L B P M U) (i : M) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.middleInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * lowerValue c entry.2)).sum

/-- Value of an upper product gate before relabelling the gate types. -/
def upperValue (c : IndexedDepth5Circuit K n L B P M U) (i : U) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.upperInputs i).map (fun j => middleValue c j)).prod

/-- Polynomial computed by a circuit indexed by arbitrary finite types. -/
def circuitValue (c : IndexedDepth5Circuit K n L B P M U) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  (c.outputInputs.map (fun entry =>
    MvPolynomial.C entry.1 * upperValue c entry.2)).sum

variable [Fintype L] [Fintype B] [Fintype P] [Fintype M] [Fintype U]

@[simp] theorem bottomValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card B)) :
    Problem335.bottomValue c.toDepth5Circuit i =
      c.bottomValue ((Fintype.equivFin B).symm i) := by
  simp [Problem335.bottomValue, toDepth5Circuit, bottomValue,
    List.map_map, Function.comp_def]

@[simp] theorem lowerValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card P)) :
    Problem335.lowerValue c.toDepth5Circuit i =
      c.lowerValue ((Fintype.equivFin P).symm i) := by
  simp [Problem335.lowerValue, lowerValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.bottomValue, bottomValue]

@[simp] theorem middleValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card M)) :
    Problem335.middleValue c.toDepth5Circuit i =
      c.middleValue ((Fintype.equivFin M).symm i) := by
  simp [Problem335.middleValue, middleValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.lowerValue, lowerValue,
    Problem335.bottomValue, bottomValue]

@[simp] theorem upperValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card U)) :
    Problem335.upperValue c.toDepth5Circuit i =
      c.upperValue ((Fintype.equivFin U).symm i) := by
  simp [Problem335.upperValue, upperValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.middleValue, middleValue,
    Problem335.lowerValue, lowerValue, Problem335.bottomValue, bottomValue]

@[simp] theorem circuitValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    Problem335.circuitValue c.toDepth5Circuit = c.circuitValue := by
  simp [Problem335.circuitValue, circuitValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.upperValue, upperValue,
    Problem335.middleValue, middleValue, Problem335.lowerValue, lowerValue,
    Problem335.bottomValue, bottomValue]

end IndexedDepth5Circuit
end Problem335

end

end OAI
