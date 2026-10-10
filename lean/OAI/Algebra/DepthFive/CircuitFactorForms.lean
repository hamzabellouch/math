import OAI.Algebra.DepthFive.CircuitDegreeBounds
import OAI.Algebra.DepthFive.Homogeneity
import OAI.Algebra.DepthFive.ProductNormalization

namespace OAI

noncomputable section

namespace Problem335
universe u
variable {K : Type u} [CommSemiring K] {n : ℕ}

/-- A lower product computes a scalar times exactly its formal degree many
homogeneous linear forms, with repeated inputs retained as repeated factors. -/
theorem lowerValue_normal_form (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    ∃ a : K, ∃ factors : List (MvPolynomial (Fin n × Fin n × Fin n) K),
      factors.length = ((c.lowerInputs i).map c.bottomDegree).sum ∧
      (∀ p ∈ factors, p.IsHomogeneous 1) ∧
      lowerValue c i = MvPolynomial.C a * factors.prod := by
  let l := (c.lowerInputs i).map fun j => (bottomValue c j, c.bottomDegree j)
  have hl : ∀ q ∈ l, q.1.IsHomogeneous q.2 := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    exact bottomValue_isHomogeneous c j
  have hle : ∀ q ∈ l, q.2 ≤ 1 := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    exact bottomDegree_le_one c j
  obtain ⟨a, factors, hlen, hhom, hval⟩ := homogeneous_product_linear_factors l hl hle
  exact ⟨a, factors, by simpa [l, Function.comp_def] using hlen, hhom,
    by simpa [l, lowerValue, Function.comp_def] using hval⟩

/-- A weighted term of a middle sum has a linear-factor form of the middle
sum's assigned degree, even for a zero coefficient or zero product. -/
theorem middle_input_normal_form (c : Depth5Circuit K n) (i : Fin c.middleCount)
    (entry : K × Fin c.lowerCount) (hentry : entry ∈ c.middleInputs i) :
    ∃ a : K, ∃ factors : List (MvPolynomial (Fin n × Fin n × Fin n) K),
      factors.length = c.middleDegree i ∧
      (∀ p ∈ factors, p.IsHomogeneous 1) ∧
      MvPolynomial.C entry.1 * lowerValue c entry.2 =
        MvPolynomial.C a * factors.prod := by
  obtain ⟨a, factors, hlen, hhom, hval⟩ := lowerValue_normal_form c entry.2
  refine ⟨entry.1 * a, factors, hlen.trans (c.middleHomogeneous i entry hentry), hhom, ?_⟩
  simp [hval, mul_assoc]

end Problem335

end

end OAI
