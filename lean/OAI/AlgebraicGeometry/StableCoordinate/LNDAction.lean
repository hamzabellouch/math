import OAI.AlgebraicGeometry.StableCoordinate.LNDExponential
import OAI.AlgebraicGeometry.StableCoordinate.CoactionAction
import OAI.AlgebraicGeometry.StableCoordinate.LNDExponentialLaw

namespace OAI

/-!
# The algebraic additive action of a locally nilpotent derivation

This file combines the finite polynomial exponential with its proved additive
group law. It constructs an actual polynomial coaction from any locally
nilpotent derivation in characteristic zero and proves both round-trip laws.
-/

noncomputable section

namespace StableCoordinate

open Polynomial
open CoactionLND (PolynomialAdditiveAction)

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- The algebraic additive action corresponding to a locally nilpotent derivation. -/
def exponentialAction (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    PolynomialAdditiveAction k A :=
  PolynomialAdditiveAction.ofCoeffLaw (LNDExponential.exponential D hD)
    (LNDExponential.coeff_exponential_zero D hD)
    (LNDExponentialLaw.coefficient_iterative D
      (LNDExponential.exponential D hD) (LNDExponential.coeff_exponential D hD))

@[simp] theorem exponentialAction_toAlgHom
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    (exponentialAction D hD).toAlgHom = LNDExponential.exponential D hD := rfl

/-- Differentiating the exponential algebraic action recovers the derivation. -/
@[simp] theorem exponentialAction_derivation
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    (exponentialAction D hD).derivation = D := by
  ext a
  exact LNDExponential.coeff_exponential_one D hD a

/-- Full polynomial coassociativity, not merely the coefficient specification. -/
theorem exponentialAction_group_law
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (LNDExponential.exponential D hD a).map (LNDExponential.exponential D hD).toRingHom =
      taylor (X : A[X]) ((LNDExponential.exponential D hD a).map C) :=
  (exponentialAction D hD).coassoc a

/-- Action invariants are exactly elements annihilated by the derivation.
No domain hypothesis is required here. -/
theorem exponentialAction_fixed_iff
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (exponentialAction D hD).toAlgHom a = C a ↔ D a = 0 :=
  LNDExponentialLaw.fixed_iff D (LNDExponential.exponential D hD)
    (LNDExponential.coeff_exponential D hD) a

/-- A polynomial additive action is recovered by exponentiating its
infinitesimal derivation, over every characteristic-zero field algebra. -/
theorem exponential_derivation_eq (ρ : PolynomialAdditiveAction k A) :
    LNDExponential.exponential ρ.derivation ρ.locallyNilpotent = ρ.toAlgHom := by
  ext a n
  calc
    _ = ((n.factorial : k)⁻¹) • (ρ.derivation : A → A)^[n] a :=
      LNDExponential.coeff_exponential ρ.derivation ρ.locallyNilpotent a n
    _ = ((n.factorial : k)⁻¹) • (n.factorial • (ρ.toAlgHom a).coeff n) := by
      rw [ρ.iterate_derivation]
    _ = (ρ.toAlgHom a).coeff n := by
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul]
      have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      rw [inv_mul_cancel₀ hn, one_smul]

/-- Existence of the action is unconditional once local nilpotence is proved. -/
theorem exists_additiveCoaction_of_locallyNilpotent
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    ∃ ρ : PolynomialAdditiveAction k A, ρ.derivation = D :=
  ⟨exponentialAction D hD, exponentialAction_derivation D hD⟩

omit [CharZero k] in
/-- Equality of additive coactions is determined by their actual algebra maps. -/
theorem additiveCoaction_ext {ρ σ : PolynomialAdditiveAction k A}
    (h : ρ.toAlgHom = σ.toAlgHom) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- The full characteristic-zero correspondence between locally nilpotent
algebra derivations and algebraic additive polynomial coactions. -/
def locallyNilpotentEquivAdditiveCoaction :
    {D : Derivation k A A // IsLocallyNilpotent D} ≃ PolynomialAdditiveAction k A where
  toFun D := exponentialAction D.1 D.2
  invFun ρ := ⟨ρ.derivation, ρ.locallyNilpotent⟩
  left_inv D := by
    apply Subtype.ext
    exact exponentialAction_derivation D.1 D.2
  right_inv ρ := additiveCoaction_ext (exponential_derivation_eq ρ)

section Naturality
variable {B : Type*} [CommRing B] [Algebra k B]

omit [CharZero k] in
/-- Intertwining derivations intertwines every iterate. -/
theorem derivation_iterate_naturality
    (D : Derivation k A A) (E : Derivation k B B) (f : A →ₐ[k] B)
    (h : ∀ a, E (f a) = f (D a)) (n : ℕ) (a : A) :
    (E : B → B)^[n] (f a) = f ((D : A → A)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h, Function.iterate_succ_apply']

/-- A homomorphism intertwining locally nilpotent derivations is equivariant
for the corresponding algebraic additive actions. -/
theorem exponentialAction_naturality
    (D : Derivation k A A) (E : Derivation k B B)
    (hD : IsLocallyNilpotent D) (hE : IsLocallyNilpotent E)
    (f : A →ₐ[k] B) (h : ∀ a, E (f a) = f (D a)) (a : A) :
    (exponentialAction E hE).toAlgHom (f a) =
      ((exponentialAction D hD).toAlgHom a).map f.toRingHom := by
  ext n
  simp only [exponentialAction_toAlgHom, LNDExponential.coeff_exponential,
    coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    derivation_iterate_naturality D E f h]
  exact (f.toLinearMap.map_smul _ _).symm

end Naturality

end StableCoordinate

end

end OAI
