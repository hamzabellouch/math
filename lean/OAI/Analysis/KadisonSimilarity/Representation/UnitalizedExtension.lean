import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension
import Mathlib.Analysis.CStarAlgebra.Unitization

namespace OAI

/-! Extension by zero is a nonunital star homomorphism. Its unitization
provides a genuine representation whose distinguished projection recovers
the original Hilbert subspace. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

def isometricExtensionHom : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (K →L[ℂ] K) where
  toFun := isometricExtension J
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    simp [isometricExtension]
  map_add' := isometricExtension_add J
  map_mul' := isometricExtension_mul J
  map_smul' := by
    intro c T
    apply ContinuousLinearMap.ext
    intro x
    simp [isometricExtension]
  map_star' := isometricExtension_star J

variable {B : Type*} [CStarAlgebra B] (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem separable_unitization [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.SeparableSpace (Unitization ℂ B) :=
  (Unitization.uniformEquivProd.symm.surjective.denseRange).separableSpace
    Unitization.uniformEquivProd.symm.continuous

/-- A unital representation retaining the zero extension of every original
algebra element. The added unit acts on the full ambient Hilbert space. -/
def unitalizedExtension : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  Unitization.starLift ((isometricExtensionHom J).comp σ.toNonUnitalStarAlgHom)

@[simp] theorem unitalizedExtension_inr (b : B) :
    unitalizedExtension J σ (Unitization.inr b) = isometricExtension J (σ b) := by
  change algebraMap ℂ (K →L[ℂ] K) 0 + isometricExtension J (σ b) = _
  simp

theorem unitalizedExtension_apply (b : Unitization ℂ B) :
    unitalizedExtension J σ b = b.fst • (1 : K →L[ℂ] K) +
      isometricExtension J (σ b.snd) := by
  change algebraMap ℂ (K →L[ℂ] K) b.fst + isometricExtension J (σ b.snd) = _
  rw [Algebra.algebraMap_eq_smul_one]

/-- The old unit becomes the orthogonal range projection of the embedding. -/
theorem unitalizedExtension_old_unit :
    unitalizedExtension J σ (Unitization.inr (1 : B)) =
      J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint := by
  rw [unitalizedExtension_inr, map_one]
  rfl

theorem unitalizedExtension_commutes (R : K →L[ℂ] K)
    (hR : ∀ b, isometricExtension J (σ b) * R = R * isometricExtension J (σ b))
    (b : Unitization ℂ B) :
    unitalizedExtension J σ b * R = R * unitalizedExtension J σ b := by
  rw [unitalizedExtension_apply, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hR]

end KadisonSimilarity

end

end OAI
