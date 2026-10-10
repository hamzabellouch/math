import OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations

namespace OAI

universe uR uS uT

/-!
# Changing coefficients in an actual cyclic group ring

The group coordinate is retained unchanged. Character evaluation and augmentation
commute with this coefficient map, including localization of the away ring.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open PrimeCharacterEvaluations

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]

/-- Map coefficients and retain the same cyclic basis. -/
def coefficientMap (φ : R →+* S) (n : ℕ) : Elem R n →+* Elem S n :=
  weightedProjection φ (AddMonoidHom.id (ZMod n)) 1

@[simp] theorem coefficientMap_single (φ : R →+* S) (n : ℕ)
    (a : ZMod n) (r : R) :
    coefficientMap φ n (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a (φ r) := by
  simp [coefficientMap, weightedProjection_single]

@[simp] theorem coefficientMap_scalar (φ : R →+* S) (n : ℕ) (r : R) :
    coefficientMap φ n (scalar n r) = scalar n (φ r) :=
  weightedProjection_scalar φ (AddMonoidHom.id (ZMod n)) 1 r

/-- Bundled naturality; no root-of-unity or nonzero-modulus premise is needed. -/
theorem evaluate_coefficientMap_hom (φ : R →+* S) (ψ : S →+* T) (n : ℕ)
    (χ : Multiplicative (ZMod n) →* T) :
    (evaluate ψ χ).comp (coefficientMap φ n) = evaluate (ψ.comp φ) χ := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]
  · intro a
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]

theorem evaluate_coefficientMap (φ : R →+* S) (ψ : S →+* T) {n : ℕ}
    (χ : Multiplicative (ZMod n) →* T) (F : Elem R n) :
    evaluate ψ χ (coefficientMap φ n F) = evaluate (ψ.comp φ) χ F :=
  congrArg (fun f : Elem R n →+* T => f F) (evaluate_coefficientMap_hom φ ψ n χ)

@[simp] theorem augmentation_coefficientMap (φ : R →+* S) (n : ℕ) [NeZero n]
    (F : Elem R n) :
    augmentation n (coefficientMap φ n F) = φ (augmentation n F) := by
  calc
    augmentation n (coefficientMap φ n F) =
        evaluate (RingHom.id S) (1 : Multiplicative (ZMod n) →* S)
          (coefficientMap φ n F) := by
            simpa only [RingHom.id_apply] using
              (evaluate_trivial_eq_augmentation (R := S) (S := S) (n := n)
                (RingHom.id S) (coefficientMap φ n F)).symm
    _ = evaluate ((RingHom.id S).comp φ) (1 : Multiplicative (ZMod n) →* S) F :=
      evaluate_coefficientMap φ (RingHom.id S) 1 F
    _ = φ (augmentation n F) := by
      simpa only [RingHom.id_comp] using evaluate_trivial_eq_augmentation φ F

end CirculantHadamard.CyclicRing

end

end OAI
