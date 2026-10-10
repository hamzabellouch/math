import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section
universe u v w

namespace Problem335

namespace D5Leaf

def mapCoefficients {K : Type u} {L : Type v} {n : ℕ}
    (f : K → L) : D5Leaf K n → D5Leaf L n
  | .scalar a => .scalar (f a)
  | .variable x => .variable x

@[simp] theorem degree_mapCoefficients {K : Type u} {L : Type v} {n : ℕ}
    (f : K → L) (x : D5Leaf K n) :
    d5LeafDegree (mapCoefficients f x) = d5LeafDegree x := by
  cases x <;> rfl

@[simp] theorem mapCoefficients_id {K : Type u} {n : ℕ} (x : D5Leaf K n) :
    mapCoefficients id x = x := by cases x <;> rfl

@[simp] theorem mapCoefficients_comp {K : Type u} {L : Type v} {M : Type w}
    {n : ℕ} (f : K → L) (g : L → M) (x : D5Leaf K n) :
    mapCoefficients g (mapCoefficients f x) = mapCoefficients (g ∘ f) x := by
  cases x <;> rfl

end D5Leaf

/-- Pure coefficient relabeling; no algebraic properties are needed for syntactic homogeneity. -/
def Depth5Circuit.mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) : Depth5Circuit L n where
  leafCount := c.leafCount
  leaves := fun i => D5Leaf.mapCoefficients f (c.leaves i)
  bottomCount := c.bottomCount
  bottomInputs := fun i => (c.bottomInputs i).map (fun e => (f e.1, e.2))
  bottomDegree := c.bottomDegree
  bottomHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa using c.bottomHomogeneous i e he
  bottomEmpty := by
    intro i h
    exact c.bottomEmpty i (List.map_eq_nil_iff.mp h)
  lowerCount := c.lowerCount
  lowerInputs := c.lowerInputs
  middleCount := c.middleCount
  middleInputs := fun i => (c.middleInputs i).map (fun e => (f e.1, e.2))
  middleDegree := c.middleDegree
  middleHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact c.middleHomogeneous i e he
  middleEmpty := by
    intro i h
    exact c.middleEmpty i (List.map_eq_nil_iff.mp h)
  upperCount := c.upperCount
  upperInputs := c.upperInputs
  outputInputs := c.outputInputs.map (fun e => (f e.1, e.2))
  outputDegree := c.outputDegree
  outputHomogeneous := by
    intro entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact c.outputHomogeneous e he
  outputEmpty := by
    intro h
    exact c.outputEmpty (List.map_eq_nil_iff.mp h)

@[simp] theorem Depth5Circuit.lowerInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    (c.mapCoefficients f).lowerInputs i = c.lowerInputs i := rfl

@[simp] theorem Depth5Circuit.middleInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    (c.mapCoefficients f).middleInputs i =
      (c.middleInputs i).map (fun e => (f e.1, e.2)) := rfl

@[simp] theorem Depth5Circuit.upperInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    (c.mapCoefficients f).upperInputs i = c.upperInputs i := rfl

@[simp] theorem Depth5Circuit.outputInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) :
    (c.mapCoefficients f).outputInputs =
      c.outputInputs.map (fun e => (f e.1, e.2)) := rfl

@[simp] theorem circuitSize_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) :
    circuitSize (c.mapCoefficients f) = circuitSize c := rfl

@[simp] theorem d5LeafValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (x : D5Leaf K n) :
    d5LeafValue (x.mapCoefficients f) = MvPolynomial.map f (d5LeafValue x) := by
  cases x <;> simp [D5Leaf.mapCoefficients, d5LeafValue]

@[simp] theorem bottomValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    bottomValue (c.mapCoefficients f) i = MvPolynomial.map f (bottomValue c i) := by
  simp [bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum]

@[simp] theorem lowerValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    lowerValue (c.mapCoefficients f) i = MvPolynomial.map f (lowerValue c i) := by
  simp [lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem middleValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    middleValue (c.mapCoefficients f) i = MvPolynomial.map f (middleValue c i) := by
  simp [middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem upperValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    upperValue (c.mapCoefficients f) i = MvPolynomial.map f (upperValue c i) := by
  simp [upperValue, middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem circuitValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) :
    circuitValue (c.mapCoefficients f) = MvPolynomial.map f (circuitValue c) := by
  simp [circuitValue, upperValue, middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]
@[simp] theorem Depth5Circuit.mapCoefficients_id {K : Type u}
    [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n) :
    c.mapCoefficients id = c := by
  cases c
  simp [Depth5Circuit.mapCoefficients]

@[simp] theorem Depth5Circuit.mapCoefficients_comp {K : Type u} {L : Type v}
    {M : Type w} [CommSemiring K] [CommSemiring L] [CommSemiring M]
    {n : ℕ} (f : K → L) (g : L → M) (c : Depth5Circuit K n) :
    (c.mapCoefficients f).mapCoefficients g = c.mapCoefficients (g ∘ f) := by
  cases c
  simp [Depth5Circuit.mapCoefficients, List.map_map, Function.comp_def]

end Problem335

end

end OAI
