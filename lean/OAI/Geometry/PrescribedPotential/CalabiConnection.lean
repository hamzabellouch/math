import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerSecondDerivatives

namespace OAI

/-! Calabi Connection. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus

structure LocalKaehlerField (n : ℕ) where
  domain : Set (V n)
  isOpen : IsOpen domain
  matrix : V n → Matrix (Fin n) (Fin n) ℂ
  smooth : ContDiffOn ℝ ∞ matrix domain
  positive : ∀ z ∈ domain, (matrix z).PosDef
  closed : ∀ y ∈ domain, ∀ u v w : V n,
    fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (matrix q) v w) y u +
    fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (matrix q) w u) y v +
    fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (matrix q) u v) y w = 0

namespace LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

def connection (j : Fin n) (z : V n) : Matrix (Fin n) (Fin n) ℂ :=
  (K.matrix z)⁻¹ * mderiv (-Complex.I) (e j) K.matrix z

def curvature (i j : Fin n) : V n → Matrix (Fin n) (Fin n) ℂ :=
  mderiv Complex.I (e i) (K.connection j)

def logDet : V n → ℝ := fun y => Real.log (K.matrix y).det.re

def ricciHessian (z : V n) : Matrix (Fin n) (Fin n) ℂ :=
  PotentialKaehler.potentialMatrix K.logDet z

lemma inverse_smooth : ContDiffOn ℝ ∞ (fun y => (K.matrix y)⁻¹) K.domain :=
  MatrixSmoothGeneral.inverse K.smooth (fun y hy => ne_of_gt (K.positive y hy).det_pos)

lemma connection_smooth (j : Fin n) : ContDiffOn ℝ ∞ (K.connection j) K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  exact matrix_smooth_mul (K.inverse_smooth.contDiffAt (K.isOpen.mem_nhds hz))
    (mderiv_smooth (K.smooth.contDiffAt (K.isOpen.mem_nhds hz)) _ _)

lemma logDet_smooth : ContDiffOn ℝ ∞ K.logDet K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  exact (Complex.reCLM.contDiff.contDiffAt.comp z
    (determinant_smooth.contDiffAt.comp z (K.smooth.contDiffAt (K.isOpen.mem_nhds hz)))).log
      (ne_of_gt (Complex.pos_iff.mp (K.positive z hz).det_pos).1)

lemma connection_symmetric {z : V n} (hz : z ∈ K.domain) (i j k : Fin n) :
    K.connection i z k j = K.connection j z k i := by
  unfold connection
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact closed_dz_symmetry K.isOpen K.smooth (fun y hy => (K.positive y hy).isHermitian)
    K.closed hz a j i

lemma curvature_formula {z : V n} (hz : z ∈ K.domain) (i j : Fin n) :
    K.curvature i j z = (K.matrix z)⁻¹ *
      (mderiv Complex.I (e i) (mderiv (-Complex.I) (e j) K.matrix) z -
        mderiv Complex.I (e i) K.matrix z * (K.matrix z)⁻¹ *
          mderiv (-Complex.I) (e j) K.matrix z) := by
  have hs := K.smooth.contDiffAt (K.isOpen.mem_nhds hz)
  unfold curvature connection
  rw [mderiv_mul (K.inverse_smooth.contDiffAt (K.isOpen.mem_nhds hz))
    (mderiv_smooth hs _ _), mderiv_inverse K.isOpen K.smooth
      (fun y hy => ne_of_gt (K.positive y hy).det_pos) hz]
  noncomm_ring

lemma ricciHessian_trace {z : V n} (hz : z ∈ K.domain) (i j : Fin n) :
    K.ricciHessian z i j = (K.curvature i j z).trace := by
  rw [ricciHessian,potentialMatrix_eq_dzbar_dz (K.logDet_smooth.contDiffAt (K.isOpen.mem_nhds hz))]
  change dzbar (e i) (dz (e j) (fun y => (K.logDet y:ℂ))) z = _
  have he : dz (e j) (fun y => (K.logDet y:ℂ)) =ᶠ[𝓝 z]
      (fun y => (K.connection j y).trace) := by
    filter_upwards [K.isOpen.mem_nhds hz] with y hy
    exact wderiv_logdet K.isOpen K.smooth K.positive hy _ _
  rw [show dzbar (e i) (dz (e j) (fun y => (K.logDet y:ℂ))) z =
    dzbar (e i) (fun y => (K.connection j y).trace) z from wderiv_congr he _ _]
  exact mderiv_trace (K.connection_smooth j |>.contDiffAt (K.isOpen.mem_nhds hz)) _ _

lemma curvature_contraction_at_one {z : V n} (hz : z ∈ K.domain)
    (hM : K.matrix z = 1) : ∑ k, K.curvature k k z = K.ricciHessian z := by
  have hc := ricci_cancellation_at_one K.isOpen K.smooth K.positive K.closed hz hM
  have he : (∑ k, K.curvature k k z) =
      (∑ k, mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) K.matrix) z) -
      ∑ k, mderiv Complex.I (e k) K.matrix z*mderiv (-Complex.I) (e k) K.matrix z := by
    simp only [K.curvature_formula hz, hM,inv_one,one_mul,mul_one,Finset.sum_sub_distrib]
  rw [he,hc,add_sub_cancel_right]
  rfl
end LocalKaehlerField
end KaehlerCalculus

end
end

end OAI
