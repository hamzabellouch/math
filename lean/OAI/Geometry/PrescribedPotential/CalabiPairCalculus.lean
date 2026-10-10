import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiCovariant
import OAI.Geometry.PrescribedPotential.CalabiTensorAlgebra
import OAI.Geometry.PrescribedPotential.MatrixTensorCalculus

namespace OAI

/-! Calabi Pair Calculus. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma calabi_pair_matrix_trace_smooth {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) : ContDiffAt ℝ ∞ (fun y => (M y).trace) z :=
  ContDiffAt.sum (fun i _ => entry_smooth hM i i)

lemma tensorPair_smooth {P M : V n → Matrix (Fin n) (Fin n) ℂ}
    {T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hP : ContDiffAt ℝ ∞ P z) (hM : ContDiffAt ℝ ∞ M z)
    (hT : ∀ i, ContDiffAt ℝ ∞ (T i) z) (hU : ∀ i, ContDiffAt ℝ ∞ (U i) z) :
    ContDiffAt ℝ ∞ (fun y => tensorPairAt (P y) (M y) (fun i => T i y) (fun i => U i y)) z := by
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    (entry_smooth hP i j).mul (calabi_pair_matrix_trace_smooth (matrix_smooth_mul
      (matrix_smooth_mul (matrix_smooth_mul (hT i) hP) (matrix_smooth_conjTranspose (hU j))) hM))))

namespace LocalKaehlerField
variable (K : LocalKaehlerField n)

def tensorPair (T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) : ℂ :=
  tensorPairAt (K.matrix z)⁻¹ (K.matrix z) (fun i => T i z) (fun i => U i z)

lemma tensorPair_smoothOn {T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ i, ContDiffOn ℝ ∞ (T i) K.domain) (hU : ∀ i, ContDiffOn ℝ ∞ (U i) K.domain) :
    ContDiffOn ℝ ∞ (K.tensorPair T U) K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  exact tensorPair_smooth (K.inverse_smooth.contDiffAt (K.isOpen.mem_nhds hz))
    (K.smooth.contDiffAt (K.isOpen.mem_nhds hz))
    (fun i => (hT i).contDiffAt (K.isOpen.mem_nhds hz))
    (fun i => (hU i).contDiffAt (K.isOpen.mem_nhds hz))

lemma matrix_hol {z : V n} (hz : z ∈ K.domain) (k : Fin n) :
    mderiv (-Complex.I) (e k) K.matrix z = K.matrix z*K.connection k z := by
  rw [connection,← mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos)),one_mul]

lemma inverse_hol {z : V n} (hz : z ∈ K.domain) (k : Fin n) :
    mderiv (-Complex.I) (e k) (fun y => (K.matrix y)⁻¹) z =
      -K.connection k z*(K.matrix z)⁻¹ := by
  rw [mderiv_inverse K.isOpen K.smooth (fun y hy => ne_of_gt (K.positive y hy).det_pos) hz]
  simp only [connection,neg_mul]

lemma tensorPair_hol {T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ i, ContDiffOn ℝ ∞ (T i) K.domain) (hU : ∀ i, ContDiffOn ℝ ∞ (U i) K.domain)
    {z : V n} (hz : z ∈ K.domain) (k : Fin n) :
    dz (e k) (K.tensorPair T U) z =
      K.tensorPair (K.covHol T k) U z +
        K.tensorPair T (fun j => mderiv Complex.I (e k) (U j)) z := by
  have hn := K.isOpen.mem_nhds hz
  have hP := K.inverse_smooth.contDiffAt hn
  have hM := K.smooth.contDiffAt hn
  have ht (i) := (hT i).contDiffAt hn
  have hu (i) := (hU i).contDiffAt hn
  have hQ (i j) := matrix_smooth_mul (matrix_smooth_mul
    (matrix_smooth_mul (ht i) hP) (matrix_smooth_conjTranspose (hu j))) hM
  have he (i j) : wderiv (-Complex.I) (e k)
      (fun y => ((K.matrix y)⁻¹ i j) * (T i y*(K.matrix y)⁻¹*(U j y)ᴴ*K.matrix y).trace) z =
      (-(K.connection k z*(K.matrix z)⁻¹) i j *
        (T i z*(K.matrix z)⁻¹*(U j z)ᴴ*K.matrix z).trace +
        (K.matrix z)⁻¹ i j *
          (mderiv (-Complex.I) (e k) (T i) z*(K.matrix z)⁻¹*(U j z)ᴴ*K.matrix z -
           T i z*K.connection k z*(K.matrix z)⁻¹*(U j z)ᴴ*K.matrix z +
           T i z*(K.matrix z)⁻¹*(mderiv Complex.I (e k) (U j) z)ᴴ*K.matrix z +
           T i z*(K.matrix z)⁻¹*(U j z)ᴴ*K.matrix z*K.connection k z).trace) := by
    rw [wderiv_mul ((entry_smooth hP i j).differentiableAt (by simp))
      ((calabi_pair_matrix_trace_smooth (hQ i j)).differentiableAt (by simp)),mderiv_trace (hQ i j)]
    change mderiv (-Complex.I) (e k) (fun y => (K.matrix y)⁻¹) z i j * _ + _ = _
    rw [K.inverse_hol hz]
    simp only [neg_mul,Matrix.neg_apply]
    congr 1
    congr 1
    congr 1
    rw [mderiv_mul (matrix_smooth_mul (matrix_smooth_mul (ht i) hP)
      (matrix_smooth_conjTranspose (hu j))) hM,
      mderiv_mul (matrix_smooth_mul (ht i) hP) (matrix_smooth_conjTranspose (hu j)),
      mderiv_mul (ht i) hP,mderiv_conjTranspose (hu j),K.inverse_hol hz,K.matrix_hol hz]
    noncomm_ring
  change wderiv (-Complex.I) (e k) (fun y => ∑ i, ∑ j,
    ((K.matrix y)⁻¹ i j)*(T i y*(K.matrix y)⁻¹*(U j y)ᴴ*K.matrix y).trace) z = _
  rw [wderiv_sum Finset.univ (fun i _ => (ContDiffAt.sum (fun j _ =>
    (entry_smooth hP i j).mul (calabi_pair_matrix_trace_smooth (hQ i j)))).differentiableAt (by simp))]
  simp only [wderiv_sum Finset.univ (fun j _ => ((entry_smooth hP _ j).mul
    (calabi_pair_matrix_trace_smooth (hQ _ j))).differentiableAt (by simp)),he]
  exact covariant_pair_algebra (K.matrix z)⁻¹ (K.matrix z) (K.connection k z)
    (fun i => T i z) (fun i => U i z) (fun i => mderiv (-Complex.I) (e k) (T i) z)
    (fun i => mderiv Complex.I (e k) (U i) z)

lemma tensorPair_bar {T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ i, ContDiffOn ℝ ∞ (T i) K.domain) (hU : ∀ i, ContDiffOn ℝ ∞ (U i) K.domain)
    {z : V n} (hz : z ∈ K.domain) (k : Fin n) :
    dzbar (e k) (K.tensorPair T U) z =
      K.tensorPair (fun i => mderiv Complex.I (e k) (T i)) U z +
        K.tensorPair T (K.covHol U k) z := by
  have hc {T U : Fin n → V n → Matrix (Fin n) (Fin n) ℂ} {y : V n} (hy : y ∈ K.domain) :
      star (K.tensorPair T U y) = K.tensorPair U T y :=
    tensorPairAt_conj (K.positive y hy).isHermitian.inv (K.positive y hy).isHermitian _ _
  have he : K.tensorPair T U =ᶠ[𝓝 z] (fun y => star (K.tensorPair U T y)) := by
    filter_upwards [K.isOpen.mem_nhds hz] with y hy using (hc hy).symm
  change wderiv Complex.I (e k) (K.tensorPair T U) z = _
  rw [wderiv_congr he]
  change dzbar (e k) (fun y => star (K.tensorPair U T y)) z = _
  rw [dzbar_conj (((K.tensorPair_smoothOn hU hT).contDiffAt
    (K.isOpen.mem_nhds hz)).differentiableAt (by simp)),K.tensorPair_hol hU hT hz]
  rw [star_add,hc hz,hc hz,add_comm]
end LocalKaehlerField
end KaehlerCalculus

end
end

end OAI
