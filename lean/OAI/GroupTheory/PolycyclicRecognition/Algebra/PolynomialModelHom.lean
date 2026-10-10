import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothHomLieDifferential

namespace OAI

/-! # Smooth homomorphisms in polynomial exponential coordinates are linear -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L K : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates K]

def polynomialModelLieHom (f : L →* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) : L →ₗ⁅ℝ⁆ K :=
  Q.tangentEquiv.symm.toLieHom.comp ((homLieDifferential f hf).comp P.tangentEquiv.toLieHom)

theorem polynomialModelLieHom_apply (f : L →* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) (x : L) :
    polynomialModelLieHom f hf x = f x := by
  have h := PolynomialExponentialCoordinates.isGroupExponential_identity.map_of_mdifferentiable
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := K))
    f (hf.mdifferentiable (by simp)) x
  change f x = mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, K)) f 1 x at h
  have hd : homLieDifferential f hf (P.tangentEquiv x) = Q.tangentEquiv (f x) := by
    rw [P.tangentEquiv_apply, Q.tangentEquiv_apply]
    exact (homLieDifferential_apply f hf x).trans h.symm
  change Q.tangentEquiv.symm
    (homLieDifferential f hf (P.tangentEquiv x)) = f x
  rw [hd, Q.tangentEquiv.symm_apply_apply]

def polynomialModelLieEquiv (f : L ≃* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) : L ≃ₗ⁅ℝ⁆ K :=
  LieEquiv.ofBijective (polynomialModelLieHom f.toMonoidHom hf) (by
    have he : (polynomialModelLieHom f.toMonoidHom hf : L → K) = f :=
      funext (polynomialModelLieHom_apply f.toMonoidHom hf)
    rw [he]
    exact f.bijective)

@[simp] theorem polynomialModelLieEquiv_apply (f : L ≃* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) (x : L) :
    polynomialModelLieEquiv f hf x = f x :=
  polynomialModelLieHom_apply f.toMonoidHom hf x

end PolycyclicRecognition

end

end OAI
