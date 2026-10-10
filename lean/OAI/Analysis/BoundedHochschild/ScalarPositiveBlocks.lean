import OAI.Analysis.BoundedHochschild.ScalarMatrixActions

namespace OAI

/-! Complete contractions preserve the positive scalar-diagonal blocks
appearing in the two-by-two operator system. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

lemma scalarBlock_diagonals_nonneg (n : ℕ)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ p ∧ 0 ≤ q := by
  have hp := diagEntry_nonneg _ hX 0
  have hq := diagEntry_nonneg _ hX 1
  have hρ := scalarMatrixHom_injective (A := A) n
  constructor
  · apply (NonUnitalStarAlgHom.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hp
  · apply (NonUnitalStarAlgHom.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hq

theorem scalarPositiveBlock_transfer (T : A →ₗ[ℂ] B) (n : ℕ)
    (hT : ∀ X : CStarMatrix (Fin n) (Fin n) A, ‖X.map T‖ ≤ ‖X‖)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ positiveBlock (scalarMatrixHom B n p) (scalarMatrixHom B n q) (X.map T) := by
  obtain ⟨hp, hq⟩ := scalarBlock_diagonals_nonneg n p q X hX
  exact positiveBlock_transfer (scalarMatrixHom A n) (scalarMatrixHom B n)
    (entrywiseMatrixLinear T n) hT (entrywiseMatrixLinear_scalar_actions T n)
    p q hp hq X hX

end BoundedHochschild.KadisonRingrose

end

end OAI
