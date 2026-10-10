import OAI.Analysis.MutuallyUnbiased.Tao.TaoFamily
import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Conclusion
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicClassification

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The Tao class is excluded by the exact certificate, without choosing a
restricted phase convention for any of the six matrices. -/
theorem matrix_family_not_equivalent_tao (H : Coord → CMatrix)
    (hH : ∀ t, IsHadamard (H t))
    (hcross : ∀ t s, t ≠ s → ∀ k l,
      Complex.normSq (∑ i, H t i k * conj (H s i l)) = 6)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (H t) a = 0)
    (s : Coord) : ¬Equivalent (H s) tao := by
  intro heq
  obtain ⟨f, hc, ho, hp⟩ := equivalent_tao_average H hH hcross horder s heq
  exact TaoCertificate.tao_exclusion f hc ho hp

/-- No transition matrix of a complete mutually unbiased family can belong to
Tao's cubic equivalence class. -/
theorem complete_family_not_equivalent_tao (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : ¬Equivalent (relativeMatrix B r s) tao := by
  apply matrix_family_not_equivalent_tao (relativeMatrix B r)
  · exact relativeMatrix_isHadamard B hB r
  · exact relativeMatrix_cross B hB r
  · intro a ha ho
    exact complete_family_order_two B hB r ha ho

/-- Proposition (cubic-exclusion) in the manuscript. -/
theorem complete_family_square_not_hadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) :
    ¬IsHadamard (fun i j => relativeMatrix B r s i j ^ 2) := by
  intro hsquare
  exact complete_family_not_equivalent_tao B hB r s
    (hadamard_square_equivalent_tao (relativeMatrix_isHadamard B hB r s) hsquare)

end MUB6

end

end OAI
