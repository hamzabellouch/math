import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.RealDeterminantOrder

namespace OAI

/-! Gradient Jacobian. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped InnerProductSpace ContDiff
namespace PotentialABP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma positive_det_nonneg {L : E →ₗ[ℝ] E} (hL : L.IsPositive) : 0 ≤ L.det := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis]
  exact ((LinearMap.posSemidef_toMatrix_iff b).mpr hL).det_nonneg

lemma positive_det_mono {L M : E →ₗ[ℝ] E}
    (hL : L.IsPositive) (hML : (M-L).IsPositive) : L.det ≤ M.det := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis L, ← LinearMap.det_toMatrix b.toBasis M]
  apply real_det_mono ((LinearMap.posSemidef_toMatrix_iff b).mpr hL)
  rw [← map_sub]
  exact (LinearMap.posSemidef_toMatrix_iff b).mpr hML

lemma inner_fderiv_gradient {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (x v w : E) :
    inner ℝ (fderiv ℝ (gradient u) x v) w = fderiv ℝ (fderiv ℝ u) x v w := by
  have hd := (InnerProductSpace.toDual ℝ E).symm.hasFDerivAt.comp x
    ((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have he := hd.fderiv
  change fderiv ℝ (gradient u) x = _ at he
  rw [he]
  change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ u) x v)) w = _
  rw [← InnerProductSpace.toDual_apply_apply]
  simp

lemma gradient_hessian_symmetric {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (x : E) :
    (fderiv ℝ (gradient u) x).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (fderiv ℝ (gradient u) x v) w = inner ℝ v (fderiv ℝ (gradient u) x w)
  rw [inner_fderiv_gradient hu, real_inner_comm, inner_fderiv_gradient hu]
  exact hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top) v w

lemma gradient_hessian_positive {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {x : E}
    (hB : ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ u) x v v) :
    (fderiv ℝ (gradient u) x).toLinearMap.IsPositive := by
  refine ⟨gradient_hessian_symmetric hu x, ?_⟩
  intro v
  change 0 ≤ inner ℝ (fderiv ℝ (gradient u) x v) v
  rw [inner_fderiv_gradient hu]
  exact hB v

end PotentialABP

end
end

end OAI
