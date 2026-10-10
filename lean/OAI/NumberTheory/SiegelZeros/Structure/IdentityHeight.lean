import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.SiegelZeros.Intersection.TorusProjectiveClosure

namespace OAI

namespace SiegelZeros


noncomputable section
namespace W58
variable (K : Type*) [Field K]

theorem identityEvaluation_surjective : Function.Surjective (identityEvaluation K) := by
  intro c
  refine ⟨algebraMap (AmbientPolynomial K) (TorusRing K) (MvPolynomial.C c), ?_⟩
  simp

def identityIdeal : Ideal (TorusRing K) := RingHom.ker (identityEvaluation K)

instance identityIdeal_isMaximal : (identityIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (identityEvaluation K) (identityEvaluation_surjective K)

@[simp] theorem mem_identityIdeal (f : TorusRing K) :
    f ∈ identityIdeal K ↔ identityEvaluation K f = 0 := Iff.rfl

theorem coordinate_sub_one_mem_identityIdeal (i : Fin 4) :
    coordinate K i - 1 ∈ identityIdeal K := by simp

theorem torus_zero_ne_one : (0 : TorusRing K) ≠ 1 := by
  intro h
  have := congrArg (identityEvaluation K) h
  simp at this

abbrev IdentityLocalRing := GenericLocalRing K (identityIdeal K)

end W58




namespace WeightedTorusJets.IdentityHeight
open _root_.OAI.SiegelZeros.W58

variable (K : Type*) [Field K]

def polynomialIdentityEvaluation (n : ℕ) : MvPolynomial (Fin n) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 1)

def polynomialIdentityIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (polynomialIdentityEvaluation K n)

lemma polynomialIdentityEvaluation_surjective (n : ℕ) :
    Function.Surjective (polynomialIdentityEvaluation K n) := by
  intro a
  exact ⟨MvPolynomial.C a, by simp [polynomialIdentityEvaluation]⟩

instance polynomialIdentityIdeal_isMaximal (n : ℕ) :
    (polynomialIdentityIdeal K n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (polynomialIdentityEvaluation_surjective K n)

def stepEvaluation (n : ℕ) : Polynomial (MvPolynomial (Fin n) K) →+* K :=
  Polynomial.eval₂RingHom (polynomialIdentityEvaluation K n) 1

lemma stepEvaluation_surjective (n : ℕ) : Function.Surjective (stepEvaluation K n) := by
  intro a
  exact ⟨Polynomial.C (MvPolynomial.C a), by simp [stepEvaluation, polynomialIdentityEvaluation]⟩

lemma polynomialIdentityEvaluation_succ (n : ℕ) :
    polynomialIdentityEvaluation K (n + 1) =
      (stepEvaluation K n).comp (MvPolynomial.finSuccEquiv K n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [polynomialIdentityEvaluation, stepEvaluation, MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [polynomialIdentityEvaluation, stepEvaluation, MvPolynomial.finSuccEquiv_X_zero]
    · simp [polynomialIdentityEvaluation, stepEvaluation, MvPolynomial.finSuccEquiv_X_succ]

theorem polynomialIdentityIdeal_height (n : ℕ) :
    (polynomialIdentityIdeal K n).height = (n : ℕ∞) := by
  induction n with
  | zero =>
      have he : polynomialIdentityEvaluation K 0 =
          (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp [polynomialIdentityEvaluation]
        · intro i
          exact Fin.elim0 i
      have hker : polynomialIdentityIdeal K 0 = ⊥ := by
        apply (RingHom.injective_iff_ker_eq_bot (polynomialIdentityEvaluation K 0)).mp
        rw [he]
        exact (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).injective
      simp only [hker, Ideal.height_bot, Nat.cast_zero]
  | succ n ih =>
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := RingHom.ker (stepEvaluation K n)
      let : P.IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (stepEvaluation_surjective K n)
      let : P.LiesOver (polynomialIdentityIdeal K n) := ⟨by
        ext f
        change polynomialIdentityEvaluation K n f = 0 ↔
          stepEvaluation K n (Polynomial.C f) = 0
        simp [stepEvaluation]⟩
      have hcomap : polynomialIdentityIdeal K (n + 1) =
          P.comap (MvPolynomial.finSuccEquiv K n).toRingHom := by
        ext f
        change polynomialIdentityEvaluation K (n + 1) f = 0 ↔
          stepEvaluation K n (MvPolynomial.finSuccEquiv K n f) = 0
        rw [polynomialIdentityEvaluation_succ]; rfl
      calc
        (polynomialIdentityIdeal K (n + 1)).height = P.height := by
          rw [hcomap]
          exact (MvPolynomial.finSuccEquiv K n).toRingEquiv.height_comap P
        _ = (polynomialIdentityIdeal K n).height + 1 :=
          Polynomial.height_eq_height_add_one (polynomialIdentityIdeal K n) P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih]; simp

lemma identityIdeal_comap_polynomial :
    (identityIdeal K).comap (algebraMap (AmbientPolynomial K) (TorusRing K)) =
      polynomialIdentityIdeal K 4 := by
  ext f
  change identityEvaluation K (algebraMap (AmbientPolynomial K) (TorusRing K) f) = 0 ↔
    polynomialIdentityEvaluation K 4 f = 0
  rw [identityEvaluation_polynomial]; rfl

theorem identityIdeal_height : (identityIdeal K).height = 4 := by
  rw [← IsLocalization.height_under (Submonoid.powers (coordinateProduct K)) (identityIdeal K),
    Ideal.under, identityIdeal_comap_polynomial, polynomialIdentityIdeal_height]
  norm_num

theorem prime_ne_identity_of_height_le_three (P : Ideal (TorusRing K))
    (hP : P.height ≤ 3) : P ≠ identityIdeal K := by
  intro h
  rw [h, identityIdeal_height] at hP
  norm_num at hP

theorem not_identity_contained_of_height_le_three (P : Ideal (TorusRing K))
    (hP : P.height ≤ 3) (hPid : P ≤ identityIdeal K) : ¬ identityIdeal K ≤ P := by
  intro hidP
  exact prime_ne_identity_of_height_le_three K P hP (le_antisymm hPid hidP)

end WeightedTorusJets.IdentityHeight

end


end SiegelZeros

end OAI
