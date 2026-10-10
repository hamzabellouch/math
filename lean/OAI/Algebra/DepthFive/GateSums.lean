import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

/-- The combined coefficient of all wires from a fixed predecessor.
Wire multiplicity is absorbed into this coefficient, not charged as gates. -/
def gateCoefficient {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (inputs : List (K × ι)) (i : ι) : K :=
  (inputs.map (fun entry => if entry.2 = i then entry.1 else 0)).sum

@[simp] theorem gateCoefficient_nil {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (i : ι) : gateCoefficient ([] : List (K × ι)) i = 0 := by
  simp [gateCoefficient]

@[simp] theorem gateCoefficient_cons {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (entry : K × ι) (inputs : List (K × ι)) (i : ι) :
    gateCoefficient (entry :: inputs) i =
      (if entry.2 = i then entry.1 else 0) + gateCoefficient inputs i := by
  simp [gateCoefficient]

/-- Any finite list of weighted inputs can be regrouped over its finite gate type. -/
theorem list_weighted_sum_eq_sum {K R ι : Type*} [Semiring K] [Semiring R]
    [Fintype ι] [DecidableEq ι] (f : K →+* R) (value : ι → R)
    (inputs : List (K × ι)) :
    (inputs.map (fun entry => f entry.1 * value entry.2)).sum =
      ∑ i, f (gateCoefficient inputs i) * value i := by
  induction inputs with
  | nil => simp
  | cons entry inputs ih =>
    simp only [List.map_cons, List.sum_cons, gateCoefficient_cons,
      map_add, add_mul, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    simp [apply_ite, ite_mul]

/-- A combined coefficient vanishes if its predecessor does not occur. -/
theorem gateCoefficient_eq_zero_of_not_mem {K ι : Type*}
    [AddCommMonoid K] [DecidableEq ι] (inputs : List (K × ι)) (i : ι)
    (h : ∀ entry ∈ inputs, entry.2 ≠ i) : gateCoefficient inputs i = 0 := by
  unfold gateCoefficient
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hx
  simp [h entry hentry]

/-- A nonzero combined coefficient must come from an actual wire. -/
theorem exists_mem_of_gateCoefficient_ne_zero {K ι : Type*}
    [AddCommMonoid K] [DecidableEq ι] (inputs : List (K × ι)) (i : ι)
    (h : gateCoefficient inputs i ≠ 0) : ∃ entry ∈ inputs, entry.2 = i := by
  by_contra hn
  apply h
  apply gateCoefficient_eq_zero_of_not_mem
  intro entry hentry heq
  exact hn ⟨entry, hentry, heq⟩

theorem bottomValue_eq_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    bottomValue c i = ∑ j : Fin c.leafCount,
      MvPolynomial.C (gateCoefficient (c.bottomInputs i) j) * d5LeafValue (c.leaves j) := by
  exact list_weighted_sum_eq_sum MvPolynomial.C (fun j => d5LeafValue (c.leaves j)) _

theorem middleValue_eq_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    middleValue c i = ∑ j : Fin c.lowerCount,
      MvPolynomial.C (gateCoefficient (c.middleInputs i) j) * lowerValue c j := by
  exact list_weighted_sum_eq_sum MvPolynomial.C (lowerValue c) _

theorem circuitValue_eq_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) :
    circuitValue c = ∑ j : Fin c.upperCount,
      MvPolynomial.C (gateCoefficient c.outputInputs j) * upperValue c j := by
  exact list_weighted_sum_eq_sum MvPolynomial.C (upperValue c) _

/-- Aggregating wires preserves the bottom homogeneous-degree constraint. -/
theorem bottomDegree_of_gateCoefficient_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) (j : Fin c.leafCount)
    (h : gateCoefficient (c.bottomInputs i) j ≠ 0) :
    d5LeafDegree (c.leaves j) = c.bottomDegree i := by
  obtain ⟨entry, hentry, heq⟩ := exists_mem_of_gateCoefficient_ne_zero _ _ h
  simpa [heq] using c.bottomHomogeneous i entry hentry

/-- Aggregating wires preserves the middle homogeneous-degree constraint. -/
theorem middleDegree_of_gateCoefficient_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) (j : Fin c.lowerCount)
    (h : gateCoefficient (c.middleInputs i) j ≠ 0) :
    ((c.lowerInputs j).map c.bottomDegree).sum = c.middleDegree i := by
  obtain ⟨entry, hentry, heq⟩ := exists_mem_of_gateCoefficient_ne_zero _ _ h
  simpa [heq] using c.middleHomogeneous i entry hentry

/-- Aggregating wires preserves the output homogeneous-degree constraint. -/
theorem outputDegree_of_gateCoefficient_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (j : Fin c.upperCount)
    (h : gateCoefficient c.outputInputs j ≠ 0) :
    ((c.upperInputs j).map c.middleDegree).sum = c.outputDegree := by
  obtain ⟨entry, hentry, heq⟩ := exists_mem_of_gateCoefficient_ne_zero _ _ h
  simpa [heq] using c.outputHomogeneous entry hentry

end Problem335

end

end OAI
