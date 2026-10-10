import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Differentiating a polynomial action commuting with fiber scaling

The manuscript's lifting argument obtains a polynomial additive action on the
line-bundle torsor which commutes with its multiplicative fiber scaling. This
file proves the coefficient-level implication: differentiation at parameter
zero preserves every integral fiber-weight space. The commutation hypothesis
is an equality of genuine ring maps into a two-parameter polynomial/Laurent
ring, not a hypothesis that the differentiated map already preserves weights.
-/

noncomputable section

namespace StableCoordinate.ActionWeightDerivative

open Polynomial

section Swap

variable {A : Type*} [CommSemiring A]

/-- Interchange the ordinary polynomial parameter and the Laurent parameter. -/
def swap : Polynomial (LaurentPolynomial A) →+* LaurentPolynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (AddMonoidAlgebra.mapRingHom ℤ Polynomial.C)
    (AddMonoidAlgebra.single 0 Polynomial.X)

/-- The interchange map transposes the two coefficient indices. -/
theorem coeff_coeff_swap (p : Polynomial (LaurentPolynomial A)) (m : ℕ) (n : ℤ) :
    ((swap p).coeff n).coeff m = (p.coeff m).coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial i a =>
    simp only [swap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      AddMonoidAlgebra.single_pow, nsmul_zero, AddMonoidAlgebra.coeff_mul_single_zero,
      AddMonoidAlgebra.coeff_mapRingHom, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_monomial]
    split_ifs <;> simp_all

end Swap

section Commutation

variable {k A : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A]

/-- The parameter interchange respects an arbitrary coefficient algebra. -/
def swapAlgHom : Polynomial (LaurentPolynomial A) →ₐ[k] LaurentPolynomial (Polynomial A) where
  __ := swap
  commutes' r := by
    change swap (Polynomial.C (LaurentPolynomial.C (algebraMap k A r))) =
      LaurentPolynomial.C (Polynomial.C (algebraMap k A r))
    simp only [swap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change (AddMonoidAlgebra.mapRingHom ℤ Polynomial.C)
      (AddMonoidAlgebra.single 0 (algebraMap k A r)) =
      AddMonoidAlgebra.single 0 (Polynomial.C (algebraMap k A r))
    exact AddMonoidAlgebra.mapRingHom_single Polynomial.C 0 (algebraMap k A r)

/-- A polynomial family commutes with a Laurent weight coaction if the two
orders of applying their coefficient maps agree, after interchanging parameters. -/
def CommutesWithWeights (ρ : A →ₐ[k] LaurentPolynomial A)
    (α : A →ₐ[k] Polynomial A) : Prop :=
  ∀ a, swap (Polynomial.map ρ.toRingHom (α a)) =
    AddMonoidAlgebra.mapAlgHom ℤ α (ρ a)

/-- The two-parameter commutation identity can be read coefficient by coefficient. -/
theorem commute_coeff (ρ : A →ₐ[k] LaurentPolynomial A) (α : A →ₐ[k] Polynomial A)
    (hcomm : CommutesWithWeights ρ α) (a : A) (m : ℕ) (n : ℤ) :
    (ρ ((α a).coeff m)).coeff n = (α ((ρ a).coeff n)).coeff m := by
  have h := congrArg (fun p : LaurentPolynomial (Polynomial A) => (p.coeff n).coeff m)
    (hcomm a)
  simp only [coeff_coeff_swap, Polynomial.coeff_map,
    AddMonoidAlgebra.coeff_mapAlgHom] at h
  exact h

/-- Every parameter coefficient of an equivariant polynomial family preserves
an integral weight, including negative weights. -/
theorem coeff_preserves_weight (ρ : A →ₐ[k] LaurentPolynomial A)
    (α : A →ₐ[k] Polynomial A) (hcomm : CommutesWithWeights ρ α)
    {a : A} {n : ℤ} (ha : ρ a = AddMonoidAlgebra.single n a) (m : ℕ) :
    ρ ((α a).coeff m) = AddMonoidAlgebra.single n ((α a).coeff m) := by
  ext j
  rw [commute_coeff ρ α hcomm, ha]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp only [map_zero, Polynomial.coeff_zero]

/-- It suffices to check equivariance coefficientwise on a set of algebra
generators. This converts frame-coordinate weights into equivariance of the
whole lifted polynomial action. -/
theorem commutesWithWeights_of_generators {σ : Type*}
    (ρ : A →ₐ[k] LaurentPolynomial A) (α : A →ₐ[k] Polynomial A)
    (g : σ → A) (w : σ → ℤ) (hgen : Algebra.adjoin k (Set.range g) = ⊤)
    (hρ : ∀ i, ρ (g i) = AddMonoidAlgebra.single (w i) (g i))
    (hα : ∀ i m, ρ ((α (g i)).coeff m) =
      AddMonoidAlgebra.single (w i) ((α (g i)).coeff m)) :
    CommutesWithWeights ρ α := by
  let L : A →ₐ[k] LaurentPolynomial (Polynomial A) :=
    (swapAlgHom (k := k) (A := A)).comp ((Polynomial.mapAlgHom ρ).comp α)
  let R : A →ₐ[k] LaurentPolynomial (Polynomial A) :=
    (AddMonoidAlgebra.mapAlgHom ℤ α).comp ρ
  have heq : L = R := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro a ⟨i, rfl⟩
    apply LaurentPolynomial.ext
    intro n
    apply Polynomial.ext
    intro m
    change (((swap (Polynomial.map ρ.toRingHom (α (g i)))).coeff n).coeff m) = _
    rw [coeff_coeff_swap, Polynomial.coeff_map]
    change (ρ ((α (g i)).coeff m)).coeff n =
      ((AddMonoidAlgebra.mapAlgHom ℤ α (ρ (g i))).coeff n).coeff m
    rw [hα, hρ, AddMonoidAlgebra.mapAlgHom_single]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> simp only [Polynomial.coeff_zero]
  intro a
  exact DFunLike.congr_fun heq a

/-- Differentiation at parameter zero preserves all weights. The derivation
may be supplied by any proved additive-action/LND correspondence. -/
theorem derivation_preserves_weight (ρ : A →ₐ[k] LaurentPolynomial A)
    (α : A →ₐ[k] Polynomial A) (hcomm : CommutesWithWeights ρ α)
    (D : Derivation k A A) (hD : ∀ a, D a = (α a).coeff 1)
    {a : A} {n : ℤ} (ha : ρ a = AddMonoidAlgebra.single n a) :
    ρ (D a) = AddMonoidAlgebra.single n (D a) := by
  rw [hD]
  exact coeff_preserves_weight ρ α hcomm ha 1

end Commutation

end StableCoordinate.ActionWeightDerivative

end

end OAI
