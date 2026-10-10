import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicHomExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentCyclicEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelWords

namespace OAI

/-! # The real cyclic completion extends the given integral homomorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates M]
  [LieRing.IsNilpotent L] [LieRing.IsNilpotent M]

theorem integer_cyclic_hom_extension (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (F : PolynomialCyclicGroup A →* M)
    (hF : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, M)) ∞ (F.comp SemidirectProduct.inl)) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∃ φ : (L × ℝ) →* M, ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ z, φ (unipotentCyclicEmbedding A hA z) = F z := by
  let k := F.comp SemidirectProduct.inl
  let f := polynomialModelLieHom k hF
  let t : PolynomialCyclicGroup A := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  let u := F t
  have hf (x : L) : f x = F (SemidirectProduct.inl x) := polynomialModelLieHom_apply k hF x
  have hconj (x : L) : f (A x) = u * f x * u⁻¹ := by
    rw [hf, hf]
    have hh := SemidirectProduct.inl_aut
      (φ := integerPowerAction (PolynomialExponentialCoordinates.groupAutomorphism A))
      (Multiplicative.ofAdd (1 : ℤ)) x
    rw [map_inv] at hh
    change SemidirectProduct.inl
      (((PolynomialExponentialCoordinates.groupAutomorphism A) ^ (1 : ℤ)) x) =
        t * SemidirectProduct.inl x * t⁻¹ at hh
    have hh' := congrArg F hh
    simpa only [zpow_one, PolynomialExponentialCoordinates.groupAutomorphism_apply,
      map_mul, map_inv] using hh'
  obtain ⟨φ, hφ, hφx⟩ := nilpotent_cyclic_hom_extension A hA f u hconj
  refine ⟨φ, hφ, ?_⟩
  intro z
  rw [unipotentCyclicEmbedding_apply, hφx, hf]
  have hz : (SemidirectProduct.inr z.right : PolynomialCyclicGroup A) = t ^ z.right.toAdd := by
    rw [← map_zpow]
    congr 1
    apply Multiplicative.ext
    change z.right.toAdd = z.right.toAdd • (1 : ℤ)
    simp
  rw [← model_zpow, ← map_zpow, ← hz]
  rw [← map_mul]
  congr 1
  exact (SemidirectProduct.mk_eq_inl_mul_inr z.right z.left).symm

end PolycyclicRecognition

end

end OAI
