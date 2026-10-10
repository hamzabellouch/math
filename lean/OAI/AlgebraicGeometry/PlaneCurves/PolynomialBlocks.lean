import Mathlib.Algebra.Polynomial.Coeff
import OAI.AlgebraicGeometry.PlaneCurves.SectionBases

namespace OAI

/-!
# Polynomial coefficient blocks with positive and zero degrees
-/

section

/-! Actual polynomials with bounded degree and prescribed coefficient submodules.
The product decomposition and basis assembly are proved from coefficient extensionality. -/
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10
variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

/-- Genuine bounded polynomials, with each coefficient in its specified submodule. -/
def boundedCoefficientPolynomials (u : ℕ) (S : ℕ → Submodule R A) :
    Submodule R (Polynomial A) where
  carrier := {F | (∀ j, u < j → F.coeff j = 0) ∧ ∀ j, F.coeff j ∈ S j}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj; simp [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj]
    · intro j; simpa using (S j).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj; simp [Polynomial.coeff_smul, hF.1 j hj]
    · intro j; simpa using (S j).smul_mem a (hF.2 j)

/-- Read the complete finite tuple of actual coefficients. -/
def boundedPolynomialCoordinates (u : ℕ) (S : ℕ → Submodule R A) :
    boundedCoefficientPolynomials u S →ₗ[R] ((j : Fin (u + 1)) → S j.val) where
  toFun F j := ⟨F.val.coeff j.val, F.property.2 j.val⟩
  map_add' F G := by ext j; simp
  map_smul' a F := by ext j; simp

theorem boundedPolynomialCoordinates_injective (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Injective (boundedPolynomialCoordinates u S) := by
  intro F G h
  apply Subtype.ext
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ u
  · exact congrArg Subtype.val (congrFun h ⟨j, by omega⟩)
  · rw [F.property.1 j (by omega), G.property.1 j (by omega)]

/-- Synthesize the polynomial from its finite tuple of actual coefficients. -/
def finiteCoefficientPolynomial (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) : Polynomial A :=
  ∑ j, Polynomial.monomial j.val (a j).val

@[simp] theorem finiteCoefficientPolynomial_coeff (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (j : Fin (u + 1)) :
    (finiteCoefficientPolynomial u S a).coeff j.val = (a j).val := by
  classical
  simp [finiteCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Fin.val_inj]

theorem finiteCoefficientPolynomial_coeff_above (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (k : ℕ) (hk : u < k) :
    (finiteCoefficientPolynomial u S a).coeff k = 0 := by
  classical
  rw [finiteCoefficientPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  apply Polynomial.coeff_monomial_of_ne
  omega

theorem boundedPolynomialCoordinates_surjective (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Surjective (boundedPolynomialCoordinates u S) := by
  intro a
  have hmem : finiteCoefficientPolynomial u S a ∈ boundedCoefficientPolynomials u S := by
    constructor
    · exact finiteCoefficientPolynomial_coeff_above u S a
    · intro k
      by_cases hk : k ≤ u
      · have he := finiteCoefficientPolynomial_coeff u S a ⟨k, by omega⟩
        rw [he]
        exact (a ⟨k, by omega⟩).property
      · rw [finiteCoefficientPolynomial_coeff_above u S a k (by omega)]
        exact (S k).zero_mem
  refine ⟨⟨finiteCoefficientPolynomial u S a, hmem⟩, ?_⟩
  ext j
  exact finiteCoefficientPolynomial_coeff u S a j

/-- The direct product description is a proved linear equivalence. -/
def boundedPolynomialEquiv (u : ℕ) (S : ℕ → Submodule R A) :
    boundedCoefficientPolynomials u S ≃ₗ[R] ((j : Fin (u + 1)) → S j.val) :=
  LinearEquiv.ofBijective (boundedPolynomialCoordinates u S)
    ⟨boundedPolynomialCoordinates_injective u S, boundedPolynomialCoordinates_surjective u S⟩

/-- Bases of coefficient subspaces assemble into a basis of genuine polynomials. -/
def boundedPolynomialBasis (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val)) :
    Basis (Σ j, I j) R (boundedCoefficientPolynomials u S) :=
  (Pi.basis b).map (boundedPolynomialEquiv u S).symm

/-- The assembled basis has precisely one nonzero polynomial coefficient. -/
theorem boundedPolynomialBasis_coeff (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val))
    (j : Fin (u + 1)) (i : I j) (k : Fin (u + 1)) :
    ((boundedPolynomialBasis u S I b ⟨j, i⟩).val).coeff k.val =
      ((Pi.single (M := fun k : Fin (u + 1) => S k.val) j (b j i)) k).val := by
  classical
  change ((boundedPolynomialEquiv u S)
    ((boundedPolynomialEquiv u S).symm ((Pi.basis b) ⟨j, i⟩)) k).val = _
  rw [LinearEquiv.apply_symm_apply, Pi.basis_apply]

/-- Each actual polynomial basis vector is the indicated coefficient times X^j. -/
theorem boundedPolynomialBasis_as_monomial (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val))
    (j : Fin (u + 1)) (i : I j) :
    (boundedPolynomialBasis u S I b ⟨j, i⟩).val =
      Polynomial.monomial j.val (b j i).val := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ u
  · let kk : Fin (u + 1) := ⟨k, by omega⟩
    have h := boundedPolynomialBasis_coeff u S I b j i kk
    rw [h, Polynomial.coeff_monomial]
    by_cases he : j = kk
    · subst j
      simp [kk]
    · have hev : j.val ≠ k := fun h => he (Fin.ext h)
      simp [Pi.single_eq_of_ne (Ne.symm he), hev]
  · rw [(boundedPolynomialBasis u S I b ⟨j, i⟩).property.1 k (by omega)]
    symm
    apply Polynomial.coeff_monomial_of_ne
    omega

end Nagata.Workers.W10

end
end

end OAI
