import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection

namespace OAI

/-! Calabi Ricci Contraction. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

lemma lower_curvature_formula {z : V n} (hz : z ∈ K.domain) (i j : Fin n) :
    K.matrix z * K.curvature i j z =
      mderiv Complex.I (e i) (mderiv (-Complex.I) (e j) K.matrix) z -
        mderiv Complex.I (e i) K.matrix z * (K.matrix z)⁻¹ *
          mderiv (-Complex.I) (e j) K.matrix z := by
  rw [K.curvature_formula hz,← mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos)),one_mul]

lemma lower_curvature_symmetry {z : V n} (hz : z ∈ K.domain) (i j a b : Fin n) :
    (K.matrix z * K.curvature i j z) a b = (K.matrix z * K.curvature a b z) i j := by
  rw [K.lower_curvature_formula hz,K.lower_curvature_formula hz]
  simp only [Matrix.sub_apply]
  congr 1
  · exact closed_mixed_symmetry K.isOpen K.smooth
      (fun y hy => (K.positive y hy).isHermitian) K.closed hz a b i j
  · simp only [Matrix.mul_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    change (dzbar (e i) (fun y => K.matrix y a l) z * (K.matrix z)⁻¹ l k) *
      dz (e j) (fun y => K.matrix y k b) z =
        (dzbar (e a) (fun y => K.matrix y i l) z * (K.matrix z)⁻¹ l k) *
          dz (e b) (fun y => K.matrix y k j) z
    rw [closed_dzbar_symmetry K.isOpen K.smooth
      (fun y hy => (K.positive y hy).isHermitian) K.closed hz a l i,
      closed_dz_symmetry K.isOpen K.smooth
      (fun y hy => (K.positive y hy).isHermitian) K.closed hz k b j]

lemma ricciHessian_contraction {z : V n} (hz : z ∈ K.domain) :
    K.ricciHessian z = ∑ p, ∑ q, ((K.matrix z)⁻¹ p q) •
      (K.matrix z * K.curvature q p z) := by
  have hi : (K.matrix z)⁻¹*K.matrix z = 1 := Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos))
  ext a b
  rw [K.ricciHessian_trace hz]
  have he : K.curvature a b z = (K.matrix z)⁻¹*(K.matrix z*K.curvature a b z) := by
    rw [← mul_assoc,hi,one_mul]
  conv_lhs => rw [he]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact K.lower_curvature_symmetry hz a b q p

lemma curvature_contraction {z : V n} (hz : z ∈ K.domain) :
    (∑ p, ∑ q, ((K.matrix z)⁻¹ p q) • K.curvature q p z) =
      (K.matrix z)⁻¹ * K.ricciHessian z := by
  rw [K.ricciHessian_contraction hz]
  simp only [Matrix.mul_sum,Matrix.mul_smul,← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos)),one_mul]

lemma connection_hol_derivative {z : V n} (hz : z ∈ K.domain) (i j : Fin n) :
    mderiv (-Complex.I) (e i) (K.connection j) z =
      (K.matrix z)⁻¹ * mderiv (-Complex.I) (e i) (mderiv (-Complex.I) (e j) K.matrix) z -
        K.connection i z * K.connection j z := by
  have hs := K.smooth.contDiffAt (K.isOpen.mem_nhds hz)
  unfold connection
  rw [mderiv_mul (K.inverse_smooth.contDiffAt (K.isOpen.mem_nhds hz))
    (mderiv_smooth hs _ _), mderiv_inverse K.isOpen K.smooth
      (fun y hy => ne_of_gt (K.positive y hy).det_pos) hz]
  noncomm_ring

lemma connection_hol_flat {z : V n} (hz : z ∈ K.domain) (i j : Fin n) :
    mderiv (-Complex.I) (e i) (K.connection j) z -
      mderiv (-Complex.I) (e j) (K.connection i) z =
      K.connection j z*K.connection i z-K.connection i z*K.connection j z := by
  rw [K.connection_hol_derivative hz,K.connection_hol_derivative hz,
    mderiv_comm (K.smooth.contDiffAt (K.isOpen.mem_nhds hz)) (-Complex.I) (-Complex.I) (e i) (e j)]
  abel
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
