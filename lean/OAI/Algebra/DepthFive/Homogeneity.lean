import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- Homogeneity is preserved by a list sum, including the empty sum. -/
theorem isHomogeneous_list_sum {K : Type u} [CommSemiring K]
    {σ : Type v} {ι : Type w} (l : List ι) (f : ι → MvPolynomial σ K) (d : ℕ)
    (h : ∀ i ∈ l, (f i).IsHomogeneous d) :
    (l.map f).sum.IsHomogeneous d := by
  induction l with
  | nil => simpa using MvPolynomial.isHomogeneous_zero σ K d
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

/-- A product's formal degree is the sum of its factors' formal degrees. -/
theorem isHomogeneous_list_prod {K : Type u} [CommSemiring K]
    {σ : Type v} {ι : Type w} (l : List ι) (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (h : ∀ i ∈ l, (f i).IsHomogeneous (d i)) :
    (l.map f).prod.IsHomogeneous (l.map d).sum := by
  induction l with
  | nil => simpa using MvPolynomial.isHomogeneous_one (σ := σ) K
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

theorem d5LeafValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (x : D5Leaf K n) : (d5LeafValue x).IsHomogeneous (d5LeafDegree x) := by
  cases x with
  | scalar a => exact MvPolynomial.isHomogeneous_C _ a
  | «variable» i => exact MvPolynomial.isHomogeneous_X K i

theorem bottomValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    (bottomValue c i).IsHomogeneous (c.bottomDegree i) := by
  unfold bottomValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.bottomHomogeneous i entry hentry]
  exact (d5LeafValue_isHomogeneous (c.leaves entry.2)).C_mul entry.1

theorem lowerValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    (lowerValue c i).IsHomogeneous ((c.lowerInputs i).map c.bottomDegree).sum := by
  unfold lowerValue
  apply isHomogeneous_list_prod
  intro j _
  exact bottomValue_isHomogeneous c j

theorem middleValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    (middleValue c i).IsHomogeneous (c.middleDegree i) := by
  unfold middleValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.middleHomogeneous i entry hentry]
  exact (lowerValue_isHomogeneous c entry.2).C_mul entry.1

theorem upperValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    (upperValue c i).IsHomogeneous ((c.upperInputs i).map c.middleDegree).sum := by
  unfold upperValue
  apply isHomogeneous_list_prod
  intro j _
  exact middleValue_isHomogeneous c j

theorem circuitValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) :
    (circuitValue c).IsHomogeneous c.outputDegree := by
  unfold circuitValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.outputHomogeneous entry hentry]
  exact (upperValue_isHomogeneous c entry.2).C_mul entry.1

end Problem335

end

end OAI
