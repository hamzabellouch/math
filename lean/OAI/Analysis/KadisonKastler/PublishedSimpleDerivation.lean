import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

namespace OAI

/-! # Sakai's inner-derivation theorem, in its needed unital form

S. Sakai, *Derivations of simple C*-algebras II*, Bulletin de la Société
Mathématique de France 99 (1971), 259--263, §2, unnumbered theorem on p.260,
together with the unital specialization explained in §1 on p.259.
DOI: 10.24033/bsmf.1719. The only input is innerness of bounded derivations
of a simple unital C-star algebra. Self-adjointness of an implementer is
derived below, not included in that input.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Simplicity in the C-star sense: there are no proper nonzero closed
two-sided ideals. Nontriviality is supplied separately where used. -/
def CStarSimple (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

/-- The published theorem, with no separability assumption. -/
def PublishedSimpleDerivationInner : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A], CStarSimple A →
    ∀ D : A →L[ℂ] A,
      (∀ x y, D (x * y) = D x * y + x * D y) →
      ∃ a : A, ∀ x, D x = a * x - x * a

variable {A : Type u} [CStarAlgebra A]

/-- A commutator with a self-adjoint ambient element is anti-star
compatible. Taking the real part of any inner implementer preserves it. -/
theorem selfAdjoint_inner_implementer (D : A →L[ℂ] A)
    (hstar : ∀ x, D (star x) = -star (D x))
    {a : A} (ha : ∀ x, D x = a * x - x * a) :
    ∃ b : A, IsSelfAdjoint b ∧ ∀ x, D x = b * x - x * b := by
  have has : ∀ x, D x = star a * x - x * star a := by
    intro x
    have h := congrArg star (ha (star x))
    rw [hstar, star_neg, star_star, star_sub, star_mul, star_mul, star_star] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨(1 / 2 : ℂ) • (a + star a),
    (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self a), ?_⟩
  intro x
  calc
    D x = (1 / 2 : ℂ) • (D x + D x) := by
      rw [← two_smul ℂ (D x), smul_smul]
      norm_num
    _ = (1 / 2 : ℂ) • ((a * x - x * a) + (star a * x - x * star a)) := by
      conv_lhs => arg 2; arg 1; rw [ha]
      conv_lhs => arg 2; arg 2; rw [has]
    _ = ((1 / 2 : ℂ) • (a + star a)) * x -
        x * ((1 / 2 : ℂ) • (a + star a)) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_sub, smul_add]
      abel

theorem exists_selfAdjoint_implementer_of_published
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (D : A →L[ℂ] A)
    (hderiv : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x, D x = a * x - x * a := by
  obtain ⟨a, ha⟩ := hPublished A hSimple D hderiv
  exact selfAdjoint_inner_implementer D hstar ha

end

end KadisonKastler

end OAI
