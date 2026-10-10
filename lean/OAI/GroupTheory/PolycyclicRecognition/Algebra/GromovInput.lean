import OAI.GroupTheory.PolycyclicRecognition.Analysis.Packing
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-!
# The polynomial-growth input in height-kernel recognition

Published input: M. Gromov, *Groups of polynomial growth and expanding maps*,
Publications Mathématiques de l'IHÉS **53** (1981), 53–78, Main Theorem, p. 54,
DOI: `10.1007/BF02698687`.

`GromovPolynomialGrowthInput J` is precisely the implication needed here: a
finite symmetric generating set with polynomially bounded intrinsic word balls
gives a nilpotent subgroup of finite index. The supporting covering-to-cardinality
argument uses concrete finite word balls, with this implication as an explicit
hypothesis.
-/

namespace PolycyclicRecognition

universe u v

variable (J : Type u) [Group J]

/-- Virtual nilpotency means the existence of a nilpotent subgroup of finite index. -/
abbrev IsVirtuallyNilpotent : Prop := Group.IsVirtuallyNilpotent J

/-- Gromov's Main Theorem (1981, p. 54), specialized to the finite symmetric
word-ball formulation used by the height-kernel argument. -/
def GromovPolynomialGrowthInput [DecidableEq J] : Prop :=
  ∀ T : Finset J,
    (∀ t ∈ T, t⁻¹ ∈ T) →
    Subgroup.closure (T : Set J) = ⊤ →
    (∃ C b : ℕ, ∀ n, (wordBall T n).card ≤ C * (1 + n) ^ b) →
    IsVirtuallyNilpotent J

variable {J} [DecidableEq J]
variable {X : Type v} [PseudoMetricSpace X] [DecidableEq X]

/-- Polynomial packing and bounded multiplicity imply virtual nilpotency,
conditionally on exactly the stated polynomial-growth input of Gromov.
No undistortion condition on `J` is needed. -/
theorem virtuallyNilpotent_of_polynomial_cover
    (gromov : GromovPolynomialGrowthInput J) (T : Finset J)
    (hsymmetric : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgenerates : Subgroup.closure (T : Set J) = ⊤)
    (f : J → X) (C b M : ℕ) (centers : ℕ → Finset X)
    (hcenters : ∀ n, (centers n).card ≤ C * (1 + n) ^ b)
    (hcover : ∀ n h, h ∈ wordBall T n → ∃ c ∈ centers n, dist (f h) c ≤ 1)
    (hmultiplicity : ∀ (c : X) (A : Finset J),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M) :
    IsVirtuallyNilpotent J := by
  apply gromov T hsymmetric hgenerates
  exact ⟨C * M, b,
    wordBall_polynomial_card_bound T f C b M centers hcenters hcover hmultiplicity⟩

/-- Finite generation supplies a finite symmetric generating set by adjoining
inverses to any finite generating set. -/
theorem exists_symmetric_finite_generating_set [Group.FG J] :
    ∃ T : Finset J, (∀ t ∈ T, t⁻¹ ∈ T) ∧ Subgroup.closure (T : Set J) = ⊤ := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG J)
  refine ⟨S ∪ S.image (fun t => t⁻¹), ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      simpa only [inv_inv] using Finset.mem_union_left (S.image (fun t => t⁻¹)) hs
  · apply top_unique
    rw [← hS]
    apply Subgroup.closure_mono
    intro t ht
    exact Finset.mem_union_left _ ht

/-- If every finite symmetric generating set has polynomially many covering
balls, finite generation and Gromov's precise input yield virtual nilpotency.
The uniform multiplicity hypothesis concerns the actual map `f`. -/
theorem virtuallyNilpotent_of_finiteGeneration_polynomial_covers [Group.FG J]
    (gromov : GromovPolynomialGrowthInput J) (f : J → X) (M : ℕ)
    (hmultiplicity : ∀ (c : X) (A : Finset J),
      (∀ h ∈ A, dist (f h) c ≤ 1) → A.card ≤ M)
    (hcovers : ∀ T : Finset J, (∀ t ∈ T, t⁻¹ ∈ T) →
      Subgroup.closure (T : Set J) = ⊤ →
      ∃ (C b : ℕ) (centers : ℕ → Finset X),
        (∀ n, (centers n).card ≤ C * (1 + n) ^ b) ∧
        (∀ n h, h ∈ wordBall T n → ∃ c ∈ centers n, dist (f h) c ≤ 1)) :
    IsVirtuallyNilpotent J := by
  obtain ⟨T, hsymmetric, hgenerates⟩ := exists_symmetric_finite_generating_set (J := J)
  obtain ⟨C, b, centers, hcenters, hcover⟩ := hcovers T hsymmetric hgenerates
  exact virtuallyNilpotent_of_polynomial_cover gromov T hsymmetric hgenerates
    f C b M centers hcenters hcover hmultiplicity

end PolycyclicRecognition

end OAI
