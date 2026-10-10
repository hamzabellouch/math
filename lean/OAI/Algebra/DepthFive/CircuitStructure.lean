import OAI.Algebra.DepthFive.ProductNormalization
import OAI.Algebra.DepthFive.Homogeneity

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

universe u v w

/-- An indexed version of positive-factor normalization. The resulting list
is a sublist of the original gate occurrences, so sharing and multiplicity
are preserved. -/
theorem homogeneous_indexed_product_positive_factors
    {K : Type u} [CommSemiring K] {σ : Type v} {ι : Type w}
    (l : List ι) (p : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hl : ∀ i ∈ l, (p i).IsHomogeneous (d i)) :
    ∃ a : K, ∃ factors : List ι,
      factors.Sublist l ∧
      (∀ i ∈ factors, 0 < d i) ∧
      (factors.map d).sum = (l.map d).sum ∧
      (l.map p).prod = C a * (factors.map p).prod ∧
      factors.length ≤ (l.map d).sum := by
  obtain ⟨a, fs, hf, hd, hv, hs, hn⟩ :=
    homogeneous_product_positive_factors (l.map (fun i => (p i, d i))) (by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact hl i hi)
  obtain ⟨factors, hsub, rfl⟩ := List.sublist_map_iff.mp hs
  refine ⟨a, factors, hsub, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hf (p i, d i) (List.mem_map.mpr ⟨i, hi, rfl⟩)).1
  · simpa only [List.map_map, Function.comp_def] using hd
  · simpa only [List.map_map, Function.comp_def] using hv
  · simpa only [List.length_map, List.map_map, Function.comp_def] using hn

/-- Every upper product is a scalar multiple of positive-formal-degree
middle-gate occurrences whose degrees add to the original formal degree. -/
theorem upperValue_positive_factors
    {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    ∃ a : K, ∃ factors : List (Fin c.middleCount),
      factors.Sublist (c.upperInputs i) ∧
      (∀ j ∈ factors, 0 < c.middleDegree j) ∧
      (factors.map c.middleDegree).sum =
        ((c.upperInputs i).map c.middleDegree).sum ∧
      upperValue c i = C a * (factors.map (middleValue c)).prod ∧
      factors.length ≤ ((c.upperInputs i).map c.middleDegree).sum := by
  exact homogeneous_indexed_product_positive_factors
    (c.upperInputs i) (middleValue c) c.middleDegree
    (fun j _ => middleValue_isHomogeneous c j)

/-- For an upper gate occurring at the output, the positive factor degrees
sum to the circuit output degree, hence there are at most that many factors. -/
theorem output_term_positive_factors
    {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (entry : K × Fin c.upperCount)
    (hentry : entry ∈ c.outputInputs) :
    ∃ a : K, ∃ factors : List (Fin c.middleCount),
      factors.Sublist (c.upperInputs entry.2) ∧
      (∀ j ∈ factors, 0 < c.middleDegree j) ∧
      (factors.map c.middleDegree).sum = c.outputDegree ∧
      upperValue c entry.2 = C a * (factors.map (middleValue c)).prod ∧
      factors.length ≤ c.outputDegree := by
  simpa only [c.outputHomogeneous entry hentry] using
    upperValue_positive_factors c entry.2

end Problem335

end

end OAI
