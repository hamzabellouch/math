import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOneParameterUniqueness

namespace OAI

/-! # Uniqueness of smooth homomorphisms from a real cyclic completion -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates M]

theorem cyclicCompletionHom_ext (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∀ (φ ψ : (L × ℝ) →* M),
      ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, M)) ∞ φ →
      ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, M)) ∞ ψ →
      (∀ x : L, φ (x, 0) = ψ (x, 0)) →
      φ (0, 1) = ψ (0, 1) → φ = ψ := by
  let := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let : Monoid (L × ℝ) := (derivationSemidirectGroup D hD).toMonoid
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  intro φ ψ hφ hψ hk ht
  have haxis (s t : ℝ) : ((0, s + t) : L × ℝ) =
      (derivationSemidirectGroup D hD).mul (0, s) (0, t) := by
    rw [derivationSemidirect_mul]
    change (0, s + t) = (0 * nilpotentDerivationFlow D hD s 0, s + t)
    rw [map_zero]
    have hz : (0 : L) * 0 = 0 := by rw [← P.one_eq_zero, mul_one]
    rw [hz]
  have hφ0 : φ (0, 0) = 1 :=
    (congrArg φ (derivationSemidirect_one D hD).symm).trans φ.map_one
  have hψ0 : ψ (0, 0) = 1 :=
    (congrArg ψ (derivationSemidirect_one D hD).symm).trans ψ.map_one
  have htime (t : ℝ) : φ (0, t) = ψ (0, t) := by
    rw [polynomial_oneParameter_eq_smul (fun r => φ (0, r)) hφ0
      (fun s t => (congrArg φ (haxis s t)).trans (φ.map_mul _ _))
      (hφ.contDiff.comp (contDiff_const.prodMk contDiff_id)),
      polynomial_oneParameter_eq_smul (fun r => ψ (0, r)) hψ0
      (fun s t => (congrArg ψ (haxis s t)).trans (ψ.map_mul _ _))
      (hψ.contDiff.comp (contDiff_const.prodMk contDiff_id)), ht]
  apply MonoidHom.ext
  intro p
  have hp : p = (derivationSemidirectGroup D hD).mul (p.1, 0) (0, p.2) := by
    rw [derivationSemidirect_mul, map_zero]
    change p = (p.1 * (0 : L), 0 + p.2)
    rw [← P.one_eq_zero, mul_one, zero_add]
  calc
    φ p = φ ((derivationSemidirectGroup D hD).mul (p.1, 0) (0, p.2)) := congrArg φ hp
    _ = φ (p.1, 0) * φ (0, p.2) := φ.map_mul _ _
    _ = ψ (p.1, 0) * ψ (0, p.2) := by rw [hk, htime]
    _ = ψ ((derivationSemidirectGroup D hD).mul (p.1, 0) (0, p.2)) := (ψ.map_mul _ _).symm
    _ = ψ p := congrArg ψ hp.symm

end PolycyclicRecognition

end

end OAI
