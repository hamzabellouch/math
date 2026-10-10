import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCovariant
import OAI.Geometry.PrescribedPotential.CalabiPairCalculus

namespace OAI

/-! Calabi Bochner. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma tensorPairAt_sum_left {α : Type*} (s : Finset α)
    (P M : Matrix (Fin n) (Fin n) ℂ) (T : α → ConnectionTensor n) (U : ConnectionTensor n) :
    tensorPairAt P M (fun i => ∑ a ∈ s, T a i) U = ∑ a ∈ s, tensorPairAt P M (T a) U := by
  simp only [tensorPairAt,Matrix.sum_mul,Matrix.trace_sum,Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a ∈ s, ∑ j, P i j*(T a i*P*(U j)ᴴ*M).trace := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

lemma tensorPairAt_sum_right {α : Type*} (s : Finset α)
    (P M : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) (U : α → ConnectionTensor n) :
    tensorPairAt P M T (fun i => ∑ a ∈ s, U a i) = ∑ a ∈ s, tensorPairAt P M T (U a) := by
  simp only [tensorPairAt,Matrix.conjTranspose_sum,Matrix.sum_mul,
    Matrix.trace_sum,Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a ∈ s, ∑ j, P i j*(T i*P*(U a j)ᴴ*M).trace := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

namespace LocalKaehlerField
variable (K : LocalKaehlerField n)

lemma covHol_bar_commute {T : Fin n → V n → Matrix (Fin n) (Fin n) ℂ}
    (hT : ∀ i, ContDiffOn ℝ ∞ (T i) K.domain) {z : V n} (hz : z ∈ K.domain) (k i : Fin n) :
    K.covHol (fun j => mderiv Complex.I (e k) (T j)) k i z =
      mderiv Complex.I (e k) (K.covHol T k i) z - K.curvature k k z*T i z +
        T i z*K.curvature k k z + ∑ q, K.curvature k k z q i • T q z := by
  have hn := K.isOpen.mem_nhds hz
  have ht (j) := (hT j).contDiffAt hn
  have hg := K.connection_smooth k |>.contDiffAt hn
  have hs := ContDiffAt.sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) =>
    matrix_smooth_smul (entry_smooth hg q i) (ht q))
  unfold covHol
  rw [mderiv_sub (((mderiv_smooth (ht i) _ _).add (matrix_smooth_mul hg (ht i))).sub
      (matrix_smooth_mul (ht i) hg)) hs,
    mderiv_sub ((mderiv_smooth (ht i) _ _).add (matrix_smooth_mul hg (ht i)))
      (matrix_smooth_mul (ht i) hg),
    mderiv_add (mderiv_smooth (ht i) _ _) (matrix_smooth_mul hg (ht i)),
    mderiv_mul hg (ht i),mderiv_mul (ht i) hg,
    mderiv_sum Finset.univ (fun q _ => matrix_smooth_smul (entry_smooth hg q i) (ht q))]
  simp only [mderiv_smul (entry_smooth hg _ i) (ht _),Finset.sum_add_distrib,
    mderiv_comm (ht i) Complex.I (-Complex.I) (e k) (e k)]
  change _ = _ - (K.curvature k k z*T i z) + _ + _
  unfold curvature
  have he : (∑ q, wderiv Complex.I (e k) (fun y => K.connection k y q i) z • T q z) =
      ∑ q, mderiv Complex.I (e k) (K.connection k) z q i • T q z := rfl
  rw [he]
  abel

lemma calabi_curvature_divergence_at_one {z : V n} (hz : z ∈ K.domain)
    (hM : K.matrix z = 1) (i : Fin n) :
    (∑ k, K.covHol (K.curvature k) k i z) =
      mderiv (-Complex.I) (e i) K.ricciHessian z - K.ricciHessian z*K.connection i z := by
  have he (k : Fin n) : K.covHol (K.curvature k) k i z =
      mderiv Complex.I (e k) (K.covHol K.connection k i) z - K.curvature k k z*K.connection i z +
        K.connection i z*K.curvature k k z + ∑ q, K.curvature k k z q i • K.connection q z :=
    K.covHol_bar_commute (T := K.connection) K.connection_smooth hz k i
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Matrix.sum_mul,← Matrix.mul_sum]
  rw [K.calabi_connection_laplacian_at_one hz hM i,K.curvature_contraction_at_one hz hM]
  have hs : (∑ k, ∑ q, K.curvature k k z q i • K.connection q z) =
      ∑ q, K.ricciHessian z q i • K.connection q z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_smul]
    congr 1
    simpa only [Matrix.sum_apply] using congrArg
      (fun A : Matrix (Fin n) (Fin n) ℂ => A q i) (K.curvature_contraction_at_one hz hM)
  rw [hs]
  abel

def calabiNorm (z : V n) : ℝ := (K.tensorPair K.connection K.connection z).re

lemma calabiNorm_smooth : ContDiffOn ℝ ∞ K.calabiNorm K.domain :=
  Complex.reCLM.contDiff.comp_contDiffOn (K.tensorPair_smoothOn K.connection_smooth K.connection_smooth)

lemma calabiNorm_complex {z : V n} (hz : z ∈ K.domain) :
    (K.calabiNorm z : ℂ) = K.tensorPair K.connection K.connection z := by
  apply Complex.ext
  · rfl
  · exact (tensorPairAt_self_real (K.positive z hz).isHermitian.inv
      (K.positive z hz).isHermitian _).symm

lemma calabiNorm_second {z : V n} (hz : z ∈ K.domain) (k : Fin n) :
    dzbar (e k) (dz (e k) (fun y => (K.calabiNorm y : ℂ))) z =
      K.tensorPair (fun i => mderiv Complex.I (e k) (K.covHol K.connection k i)) K.connection z +
      K.tensorPair (K.covHol K.connection k) (K.covHol K.connection k) z +
      K.tensorPair (K.curvature k) (K.curvature k) z +
      K.tensorPair K.connection (K.covHol (K.curvature k) k) z := by
  have hn := K.isOpen.mem_nhds hz
  have hc : (fun y => (K.calabiNorm y : ℂ)) =ᶠ[𝓝 z] K.tensorPair K.connection K.connection := by
    filter_upwards [hn] with y hy using K.calabiNorm_complex hy
  have hd : dz (e k) (fun y => (K.calabiNorm y : ℂ)) =ᶠ[𝓝 z]
      (fun y => K.tensorPair (K.covHol K.connection k) K.connection y +
        K.tensorPair K.connection (K.curvature k) y) := by
    filter_upwards [hn] with y hy
    have he : (fun y => (K.calabiNorm y : ℂ)) =ᶠ[𝓝 y] K.tensorPair K.connection K.connection := by
      filter_upwards [K.isOpen.mem_nhds hy] with x hx using K.calabiNorm_complex hx
    change wderiv (-Complex.I) (e k) _ y = _
    rw [wderiv_congr he]
    exact K.tensorPair_hol K.connection_smooth K.connection_smooth hy k
  change wderiv Complex.I (e k) _ z = _
  rw [wderiv_congr hd,wderiv_add
    ((K.tensorPair_smoothOn (T := K.covHol K.connection k) (U := K.connection)
      (K.covHol_smooth (T := K.connection) K.connection_smooth k) K.connection_smooth).contDiffAt hn
      |>.differentiableAt (by simp))
    ((K.tensorPair_smoothOn (T := K.connection) (U := K.curvature k) K.connection_smooth (K.curvature_smooth k)).contDiffAt hn
      |>.differentiableAt (by simp))]
  change dzbar (e k) _ z + dzbar (e k) _ z = _
  rw [K.tensorPair_bar (T := K.covHol K.connection k) (U := K.connection)
    (K.covHol_smooth (T := K.connection) K.connection_smooth k) K.connection_smooth hz,
    K.tensorPair_bar (T := K.connection) (U := K.curvature k) K.connection_smooth (K.curvature_smooth k) hz]
  exact (add_assoc _ _ _).symm

lemma calabi_bochner_at_one {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1) :
    (PotentialKaehler.potentialMatrix K.calabiNorm z).trace =
      (∑ k, tensorPairAt 1 1 (fun i => K.covHol K.connection k i z)
        (fun i => K.covHol K.connection k i z)) +
      (∑ k, tensorPairAt 1 1 (fun i => K.curvature k i z) (fun i => K.curvature k i z)) +
      tensorPairAt 1 1 (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z -
        K.connection i z*K.ricciHessian z - ∑ q, K.ricciHessian z q i • K.connection q z)
        (fun i => K.connection i z) +
      tensorPairAt 1 1 (fun i => K.connection i z)
        (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z - K.ricciHessian z*K.connection i z) := by
  change (∑ k, PotentialKaehler.potentialMatrix K.calabiNorm z k k) = _
  simp_rw [potentialMatrix_eq_dzbar_dz (K.calabiNorm_smooth.contDiffAt (K.isOpen.mem_nhds hz))]
  change (∑ k, dzbar (e k) (dz (e k) (fun y => (K.calabiNorm y : ℂ))) z) = _
  simp_rw [K.calabiNorm_second hz]
  simp only [tensorPair,hM,inv_one,Finset.sum_add_distrib]
  rw [← tensorPairAt_sum_left,← tensorPairAt_sum_right]
  simp_rw [K.calabi_connection_laplacian_at_one hz hM,K.calabi_curvature_divergence_at_one hz hM]
  abel

end LocalKaehlerField
end KaehlerCalculus

end
end

end OAI
