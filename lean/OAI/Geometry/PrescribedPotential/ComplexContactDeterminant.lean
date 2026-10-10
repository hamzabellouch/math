import Mathlib
import OAI.Geometry.PrescribedPotential.GradientJacobian

namespace OAI

/-! Complex Contact Determinant. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped InnerProductSpace ContDiff ComplexOrder
namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance complexContactDeterminantRealInnerProductSpace (d : ℕ) :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))

lemma real_det_hermitian (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    (H.toEuclideanLin.restrictScalars ℝ).det = H.det.re ^ 2 := by
  rw [LinearMap.det_restrictScalars]
  have hm : H.toEuclideanLin.det = H.det := LinearMap.det_toLpLin 2 H
  rw [hm, Algebra.norm_complex_eq]
  have him : H.det.im = 0 := by
    have he : star H.det = H.det := by
      rw [← Matrix.det_conjTranspose, hH]
    exact (Complex.conj_eq_iff_im).mp he
  simp [Complex.normSq_apply, him, pow_two]

 

lemma gradient_det_le_hermitian {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {x : E}
    (hB : ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ u) x v v)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (hdom : ∀ v : E, fderiv ℝ (fderiv ℝ u) x v v ≤
      4 * inner ℝ (H.toEuclideanLin v) v) :
    |(fderiv ℝ (gradient u) x).det| ≤ (4:ℝ)^(2*d) * H.det.re^2 := by
  let L := (fderiv ℝ (gradient u) x).toLinearMap
  let M : E →ₗ[ℝ] E := (4:ℝ) • H.toEuclideanLin.restrictScalars ℝ
  have hL : L.IsPositive := gradient_hessian_positive hu hB
  have hM : (M-L).IsPositive := by
    refine ⟨?_,?_⟩
    · exact (LinearMap.IsSymmetric.smul (by simp)
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).restrictScalars).sub hL.1
    · intro v
      change 0 ≤ inner ℝ ((4:ℝ) • H.toEuclideanLin v - fderiv ℝ (gradient u) x v) v
      rw [inner_sub_left, real_inner_smul_left, inner_fderiv_gradient hu]
      exact sub_nonneg.mpr (hdom v)
  have hn := positive_det_nonneg hL
  have hm := positive_det_mono hL hM
  change |L.det| ≤ _
  rw [abs_of_nonneg hn]
  convert hm using 1
  dsimp only [M]
  rw [LinearMap.det_smul, real_det_hermitian H hH,
    finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

end PotentialABP

end
end

end OAI
