import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiNormAlgebra
import OAI.Geometry.PrescribedPotential.FrameCompactBounds
import OAI.Geometry.PrescribedPotential.LinearFrameCalculus

namespace OAI

/-! Calabi Rescue. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def rescueSquare (D : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) : ℝ :=
  ∑ k, frameGram 1 (T k*D)

lemma rescueSquare_pos {D : Matrix (Fin n) (Fin n) ℂ} (hD : IsUnit D)
    {T : ConnectionTensor n} (hT : T ≠ 0) : 0 < rescueSquare D T := by
  obtain ⟨k,hk⟩ : ∃ k, T k ≠ 0 := by
    by_contra h
    apply hT
    funext k
    exact not_not.mp (fun hk => h ⟨k,hk⟩)
  have hkd : T k*D ≠ 0 := by
    intro he
    apply hk
    exact hD.mul_right_cancel (by simpa using he)
  unfold rescueSquare
  apply Finset.sum_pos'
  · intro i _
    simpa only [frameGram,mul_one] using (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (T i*D)).trace_nonneg).1
  · exact ⟨k,Finset.mem_univ _,frameGram_pos Matrix.PosDef.one hkd⟩

lemma rescueSquare_smul (D : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) (r : ℝ) :
    rescueSquare D (r • T) = r^2*rescueSquare D T := by
  simp only [rescueSquare,Pi.smul_apply,Matrix.smul_mul]
  change (∑ k, frameGram 1 (r • (T k*D))) = _
  simp_rw [frameGram_smul]
  rw [Finset.mul_sum]

lemma rescueSquare_continuous : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n =>
    rescueSquare p.1 p.2) := by
  unfold rescueSquare
  apply continuous_finsetSum
  intro k _
  have hc : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ConnectionTensor n => p.2 k*p.1) :=
    ((continuous_apply k).comp continuous_snd).mul continuous_fst
  apply continuousOn_univ.mp
  exact continuousOn_trace_re (((continuousOn_matrix_star hc.continuousOn).mul
    (continuous_const (y := (1 : Matrix (Fin n) (Fin n) ℂ))).continuousOn).mul hc.continuousOn)

lemma rescueSquare_compact_lower {X : Type*} [TopologicalSpace X] {L : Set X} (hL : IsCompact L)
    (D : X → Matrix (Fin n) (Fin n) ℂ) (hD : ContinuousOn D L) (hu : ∀ x ∈ L, IsUnit (D x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, ∀ T, δ*tensorSquare T ≤ rescueSquare (D x) T := by
  obtain ⟨a,ha,hbound⟩ := compact_homogeneous_positive hL (fun x T => rescueSquare (D x) T)
    ((rescueSquare_continuous.comp_continuousOn (f := fun p : X × ConnectionTensor n => (D p.1,p.2))
      ((hD.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk continuous_snd.continuousOn)))
    (fun x hx T hn => rescueSquare_pos (hu x hx) hn) (fun x _ r T => rescueSquare_smul (D x) T r)
  obtain ⟨B,hB,hSq⟩ := compact_homogeneous_bound (K := (univ : Set Unit)) isCompact_univ 2 (by decide)
    (fun (_ : Unit) (T : ConnectionTensor n) => tensorSquare T)
    (continuous_tensorSquare.comp continuous_snd).continuousOn (fun _ _ r T => tensorSquare_smul r T)
  have hBp : 0 < B+1 := by linarith
  refine ⟨a/(B+1),div_pos ha hBp,?_⟩
  intro x hx T
  have hS : tensorSquare T ≤ (B+1)*‖T‖^2 := by
    have hh := (le_abs_self (tensorSquare T)).trans (hSq () (mem_univ _) T)
    nlinarith [sq_nonneg ‖T‖]
  have hh := mul_le_mul_of_nonneg_left hS (div_nonneg ha.le hBp.le)
  have he : a/(B+1)*((B+1)*‖T‖^2) = a*‖T‖^2 := by field_simp
  exact (he ▸ hh).trans (hbound x hx T)

namespace LocalKaehlerField
variable (K : LocalKaehlerField n)

def weightedTrace (D : Matrix (Fin n) (Fin n) ℂ) (z : V n) : ℝ := (Dᴴ*K.matrix z*D).trace.re

lemma weightedTrace_smooth (D : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (K.weightedTrace D) K.domain := by
  apply K.isOpen.contDiffOn_iff.mpr
  intro z hz
  have hs := matrix_smooth_mul (matrix_smooth_mul (contDiffAt_const (c := Dᴴ))
    (K.smooth.contDiffAt (K.isOpen.mem_nhds hz))) (contDiffAt_const (c := D))
  exact Complex.reCLM.contDiff.contDiffAt.comp z (ContDiffAt.sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => entry_smooth hs i i))

lemma weightedTrace_complex (D : Matrix (Fin n) (Fin n) ℂ) {z : V n} (hz : z ∈ K.domain) :
    (K.weightedTrace D z : ℂ) = (Dᴴ*K.matrix z*D).trace := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp ((K.positive z hz).posSemidef.conjTranspose_mul_mul_same D).trace_nonneg).2

lemma weightedTrace_laplacian_at_one (D : Matrix (Fin n) (Fin n) ℂ)
    {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1) :
    (PotentialKaehler.potentialMatrix (K.weightedTrace D) z).trace.re =
      (Dᴴ*K.ricciHessian z*D).trace.re + rescueSquare D (fun k => K.connection k z) := by
  have hn := K.isOpen.mem_nhds hz
  have hs := K.smooth.contDiffAt hn
  have ht := K.weightedTrace_smooth D |>.contDiffAt hn
  have he : (fun y => (K.weightedTrace D y:ℂ)) =ᶠ[𝓝 z] (fun y => (Dᴴ*K.matrix y*D).trace) := by
    filter_upwards [hn] with y hy using K.weightedTrace_complex D hy
  have hd (k : Fin n) : dz (e k) (fun y => (K.weightedTrace D y:ℂ)) =ᶠ[𝓝 z]
      (fun y => (Dᴴ*mderiv (-Complex.I) (e k) K.matrix y*D).trace) := by
    filter_upwards [hn] with y hy
    have hey : (fun y => (K.weightedTrace D y:ℂ)) =ᶠ[𝓝 y] (fun y => (Dᴴ*K.matrix y*D).trace) := by
      filter_upwards [K.isOpen.mem_nhds hy] with x hx using K.weightedTrace_complex D hx
    change wderiv (-Complex.I) _ _ _ = _
    rw [wderiv_congr hey,mderiv_trace (matrix_smooth_mul (matrix_smooth_mul contDiffAt_const
      (K.smooth.contDiffAt (K.isOpen.mem_nhds hy))) contDiffAt_const),
      mderiv_congruence (K.smooth.contDiffAt (K.isOpen.mem_nhds hy))]
  have hdd (k : Fin n) : (PotentialKaehler.potentialMatrix (K.weightedTrace D) z) k k =
      (Dᴴ*mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) K.matrix) z*D).trace := by
    rw [potentialMatrix_eq_dzbar_dz ht]
    change wderiv Complex.I (e k) (dz (e k) (fun y => (K.weightedTrace D y:ℂ))) z = _
    rw [wderiv_congr (hd k),mderiv_trace (matrix_smooth_mul (matrix_smooth_mul contDiffAt_const
      (mderiv_smooth hs _ _)) contDiffAt_const),mderiv_congruence (mderiv_smooth hs _ _)]
  have hc := ricci_cancellation_at_one K.isOpen K.smooth K.positive K.closed hz hM
  change (∑ k, (PotentialKaehler.potentialMatrix (K.weightedTrace D) z) k k).re = _
  simp_rw [hdd]
  rw [← Matrix.trace_sum,← Matrix.sum_mul,← Matrix.mul_sum,hc,mul_add,add_mul,
    Matrix.trace_add,Complex.add_re]
  congr 1
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum,rescueSquare,frameGram,
    connection,hM,inv_one,one_mul,Matrix.conjTranspose_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  rw [mderiv_bar_eq_conjTranspose K.isOpen K.smooth (fun y hy => (K.positive y hy).isHermitian) hz]
end LocalKaehlerField
end KaehlerCalculus

end
end

end OAI
