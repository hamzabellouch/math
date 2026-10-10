import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiRicciContraction
import OAI.Geometry.PrescribedPotential.MatrixTensorCalculus

namespace OAI

/-! Calabi Covariant. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

lemma curvature_smooth (i j : Fin n) : ContDiffOn ℝ ∞ (K.curvature i j) K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  exact mderiv_smooth (K.connection_smooth j |>.contDiffAt (K.isOpen.mem_nhds hz)) _ _

lemma ricciHessian_smooth : ContDiffOn ℝ ∞ K.ricciHessian K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  exact PotentialKaehler.potentialMatrix_smooth (K.logDet_smooth.contDiffAt (K.isOpen.mem_nhds hz))

def covHol (T : Fin n → V n → Matrix (Fin n) (Fin n) ℂ) (k i : Fin n) (z : V n) :
    Matrix (Fin n) (Fin n) ℂ :=
  mderiv (-Complex.I) (e k) (T i) z + K.connection k z*T i z - T i z*K.connection k z -
    ∑ q, (K.connection k z q i) • T q z

lemma covHol_smooth {T : Fin n → V n → Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ i, ContDiffOn ℝ ∞ (T i) K.domain) (k i : Fin n) :
    ContDiffOn ℝ ∞ (K.covHol T k i) K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  have hΓ := K.connection_smooth k |>.contDiffAt (K.isOpen.mem_nhds hz)
  have ht (j) := (hT j).contDiffAt (K.isOpen.mem_nhds hz)
  exact (((mderiv_smooth (ht i) _ _).add (matrix_smooth_mul hΓ (ht i))).sub
    (matrix_smooth_mul (ht i) hΓ)).sub
      (ContDiffAt.sum (fun q _ => matrix_smooth_smul (entry_smooth hΓ q i) (ht q)))

lemma covHol_connection_swap {z : V n} (hz : z ∈ K.domain) (k i : Fin n) :
    K.covHol K.connection k i z = mderiv (-Complex.I) (e i) (K.connection k) z -
      ∑ q, (K.connection k z q i) • K.connection q z := by
  have he := K.connection_hol_flat hz k i
  unfold covHol
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  abel

lemma derivative_curvature_contraction_at_one {z : V n} (hz : z ∈ K.domain)
    (hM : K.matrix z = 1) (i : Fin n) :
    (∑ k, mderiv (-Complex.I) (e i) (K.curvature k k) z) =
      mderiv (-Complex.I) (e i) (fun y => (K.matrix y)⁻¹*K.ricciHessian y) z +
        ∑ p, ∑ q, (K.connection i z p q) • K.curvature q p z := by
  have hnh := K.isOpen.mem_nhds hz
  have hI := K.inverse_smooth.contDiffAt hnh
  have hV (p q) := K.curvature_smooth p q |>.contDiffAt hnh
  have hC := K.connection_smooth i |>.contDiffAt hnh
  have he : (fun y => ∑ p, ∑ q, ((K.matrix y)⁻¹ p q) • K.curvature q p y) =ᶠ[𝓝 z]
      (fun y => (K.matrix y)⁻¹*K.ricciHessian y) := by
    filter_upwards [hnh] with y hy
    exact K.curvature_contraction hy
  have hh := mderiv_congr he (-Complex.I) (e i)
  have hd : mderiv (-Complex.I) (e i) (fun y => (K.matrix y)⁻¹) z = -K.connection i z := by
    rw [mderiv_inverse K.isOpen K.smooth (fun y hy => ne_of_gt (K.positive y hy).det_pos) hz,
      connection,hM]
    simp only [inv_one,neg_mul,one_mul,mul_one]
  have hf (p q) : mderiv (-Complex.I) (e i)
      (fun y => ((K.matrix y)⁻¹ p q) • K.curvature q p y) z =
      -(K.connection i z p q) • K.curvature q p z +
        ((1 : Matrix (Fin n) (Fin n) ℂ) p q) • mderiv (-Complex.I) (e i) (K.curvature q p) z := by
    rw [mderiv_smul (entry_smooth hI p q) (hV q p)]
    change mderiv (-Complex.I) (e i) (fun y => (K.matrix y)⁻¹) z p q • _ + _ = _
    rw [hd,hM,inv_one]
    rfl
  rw [mderiv_sum Finset.univ (fun p _ => ContDiffAt.sum (fun q _ =>
    matrix_smooth_smul (entry_smooth hI p q) (hV q p)))] at hh
  simp only [mderiv_sum Finset.univ (fun q _ => matrix_smooth_smul (entry_smooth hI _ q) (hV q _)),hf,
    Finset.sum_add_distrib,neg_smul,Finset.sum_neg_distrib] at hh
  have hone : (∑ p, ∑ q, ((1 : Matrix (Fin n) (Fin n) ℂ) p q) •
      mderiv (-Complex.I) (e i) (K.curvature q p) z) =
      ∑ k, mderiv (-Complex.I) (e i) (K.curvature k k) z := by
    simp [Matrix.one_apply]
  rw [hone] at hh
  have hh' := congrArg (fun A => A + ∑ p, ∑ q, (K.connection i z p q) • K.curvature q p z) hh
  convert hh' using 1
  abel

lemma bar_covHol_connection {z : V n} (hz : z ∈ K.domain) (k i : Fin n) :
    mderiv Complex.I (e k) (K.covHol K.connection k i) z =
      mderiv (-Complex.I) (e i) (K.curvature k k) z -
        ∑ q, ((K.curvature k k z q i) • K.connection q z +
          (K.connection k z q i) • K.curvature k q z) := by
  have hnh := K.isOpen.mem_nhds hz
  have hG (j) := K.connection_smooth j |>.contDiffAt hnh
  have he : (K.covHol K.connection k i) =ᶠ[𝓝 z]
      (fun y => mderiv (-Complex.I) (e i) (K.connection k) y -
        ∑ q, (K.connection k y q i) • K.connection q y) := by
    filter_upwards [hnh] with y hy
    exact K.covHol_connection_swap hy k i
  rw [mderiv_congr he, mderiv_sub (mderiv_smooth (hG k) _ _)
    (ContDiffAt.sum (fun q _ => matrix_smooth_smul (entry_smooth (hG k) q i) (hG q))),
    mderiv_comm (hG k) Complex.I (-Complex.I) (e k) (e i),
    mderiv_sum Finset.univ (fun q _ => matrix_smooth_smul (entry_smooth (hG k) q i) (hG q))]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact mderiv_smul (entry_smooth (hG k) q i) (hG q) _ _

 

lemma calabi_connection_laplacian_at_one {z : V n} (hz : z ∈ K.domain)
    (hM : K.matrix z = 1) (i : Fin n) :
    (∑ k, mderiv Complex.I (e k) (K.covHol K.connection k i) z) =
      mderiv (-Complex.I) (e i) K.ricciHessian z -
        K.connection i z * K.ricciHessian z -
        ∑ q, (K.ricciHessian z q i) • K.connection q z := by
  have hc := K.curvature_contraction_at_one hz hM
  have h1 : (∑ k, ∑ q, (K.curvature k k z q i) • K.connection q z) =
      ∑ q, (K.ricciHessian z q i) • K.connection q z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_smul]
    congr 1
    simpa only [Matrix.sum_apply] using congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A q i) hc
  have h2 : (∑ k, ∑ q, (K.connection k z q i) • K.curvature k q z) =
      ∑ p, ∑ q, (K.connection i z p q) • K.curvature q p z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro k _
    rw [K.connection_symmetric hz]
  have h3 : mderiv (-Complex.I) (e i) (fun y => (K.matrix y)⁻¹*K.ricciHessian y) z =
      mderiv (-Complex.I) (e i) K.ricciHessian z - K.connection i z*K.ricciHessian z := by
    rw [mderiv_mul (K.inverse_smooth.contDiffAt (K.isOpen.mem_nhds hz))
      (K.ricciHessian_smooth.contDiffAt (K.isOpen.mem_nhds hz)),
      mderiv_inverse K.isOpen K.smooth (fun y hy => ne_of_gt (K.positive y hy).det_pos) hz,
      connection,hM]
    simp only [inv_one,neg_mul,one_mul,mul_one]
    abel
  simp only [K.bar_covHol_connection hz, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1,h2,K.derivative_curvature_contraction_at_one hz hM,h3]
  abel
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
