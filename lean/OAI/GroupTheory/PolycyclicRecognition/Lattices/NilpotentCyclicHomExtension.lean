import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentConjugationFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectIntegration

namespace OAI

/-! # Extending a nilpotent cyclic homomorphism to real time

The time-one conjugation relation supplies the full real action relation by
finite logarithms. No continuous extension is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates M]
  [LieRing.IsNilpotent L] [LieRing.IsNilpotent M]

theorem nilpotent_cyclic_hom_extension (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    ∃ φ : (L × ℝ) →* M, ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ p, φ p = f p.1 * (p.2 • u) := by
  let D := unipotentLieLogarithm A hA
  let hD := unipotentLieLogarithm_nilpotent A hA
  let := derivationSemidirectGroup D hD
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  obtain ⟨k, hk, hkexp⟩ := integrate_polynomial_nilpotent
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity L
    (inferInstance : LieRing.IsNilpotent L) (Q.tangentEquiv.toLieHom.comp f)
  have hkf (x : L) : k x = f x := (hkexp x).trans (Q.tangentEquiv_apply (f x))
  have hact (t : ℝ) (x : L) :
      k (nilpotentDerivationFlow D hD t x) =
        (t • u) * k x * (t • u)⁻¹ := by
    rw [hkf, hkf]
    exact unipotent_conjugation_flow A hA f u h t x
  have hexp (t : ℝ) : (show M from t • Q.tangentEquiv u) = t • u :=
    (Q.tangentEquiv.map_smul t u).symm.trans (Q.tangentEquiv_apply (t • u))
  let φ := derivationSemidirectHom D hD
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity k (Q.tangentEquiv u)
    (by
      intro t x
      exact (hact t x).trans
        (congrArg (fun v : M => v * k x * v⁻¹) (hexp t).symm))
  refine ⟨φ, ?_, ?_⟩
  · exact contMDiff_derivationSemidirectHom D hD _ _ k _ _ hk
  · intro p
    change k p.1 * (show M from p.2 • Q.tangentEquiv u) = _
    rw [hkf, hexp]

end PolycyclicRecognition

end

end OAI
