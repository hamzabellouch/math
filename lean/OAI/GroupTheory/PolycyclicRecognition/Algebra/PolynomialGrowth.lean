import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-!
# The polynomial-growth branch of recognition

Gromov's polynomial-growth implication gives virtual nilpotence, and finite
generation converts virtual nilpotence to virtual polycyclicity.
-/

namespace PolycyclicRecognition

variable {G X : Type*} [Group G] [DecidableEq G]
  [PseudoMetricSpace X] [DecidableEq X]

/-- Gromov's published input, combined with the proved algebraic step, turns
polynomial growth of a finite symmetric generating set into virtual polycyclicity. -/
theorem virtuallyPolycyclic_of_polynomial_word_growth
    (gromov : GromovPolynomialGrowthInput G) (T : Finset G)
    (hsymmetric : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgenerates : Subgroup.closure (T : Set G) = ⊤)
    (hgrowth : ∃ C b : ℕ, ∀ n, (wordBall T n).card ≤ C * (1 + n) ^ b) :
    IsVirtuallyPolycyclic G := by
  have : Group.FG G := Group.fg_def.mpr ⟨T, hgenerates⟩
  exact isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent G
    (gromov T hsymmetric hgenerates hgrowth)

/-- The fully checked polynomial-cover deduction needed in the nilpotent branch. -/
theorem virtuallyPolycyclic_of_polynomial_cover
    (gromov : GromovPolynomialGrowthInput G) (T : Finset G)
    (hsymmetric : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgenerates : Subgroup.closure (T : Set G) = ⊤)
    (f : G → X) (C b M : ℕ) (centers : ℕ → Finset X)
    (hcenters : ∀ n, (centers n).card ≤ C * (1 + n) ^ b)
    (hcover : ∀ n h, h ∈ wordBall T n → ∃ c ∈ centers n, dist (f h) c ≤ 1)
    (hmultiplicity : ∀ (c : X) (A : Finset G),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M) :
    IsVirtuallyPolycyclic G := by
  apply virtuallyPolycyclic_of_polynomial_word_growth gromov T hsymmetric hgenerates
  exact ⟨C * M, b,
    wordBall_polynomial_card_bound T f C b M centers hcenters hcover hmultiplicity⟩

end PolycyclicRecognition

end OAI
