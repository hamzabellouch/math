import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedNormalFrames
import OAI.Geometry.PrescribedPotential.CalabiBochner
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiFrameAlgebra
import OAI.Geometry.PrescribedPotential.CalabiNormAlgebra

namespace OAI

/-! Calabi Coordinate Coercivity. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def tensorTransport (C D : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) : ConnectionTensor n :=
  fun i => D*(∑ p, C p i • T p)*C

lemma tensorTransport_smul (C D : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (T : ConnectionTensor n) :
    tensorTransport C D (r • T) = r • tensorTransport C D T := by
  funext i
  simp only [tensorTransport,Pi.smul_apply,smul_comm (_:ℂ) r,← Finset.smul_sum,
    Matrix.mul_smul,Matrix.smul_mul]

lemma tensorTransport_zero (C D : Matrix (Fin n) (Fin n) ℂ) :
    tensorTransport C D (0 : ConnectionTensor n) = 0 := by
  funext i
  simp [tensorTransport]

lemma tensorTransport_undo {C D : Matrix (Fin n) (Fin n) ℂ}
    (hCD : C*D=1) (_hDC : D*C=1) (T : ConnectionTensor n) :
    tensorTransport D C (tensorTransport C D T) = T := by
  funext i
  unfold tensorTransport
  have he : (∑ p, D p i • (D*(∑ q, C q p • T q)*C)) =
      D*(∑ q, (C*D) q i • T q)*C := by
    calc
      _ = ∑ p, D*(∑ q, (D p i*C q p) • T q)*C := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [← smul_smul,← Finset.smul_sum,Matrix.mul_smul,Matrix.smul_mul]
      _ = D*(∑ p, ∑ q, (D p i*C q p) • T q)*C := by
        rw [Matrix.mul_sum,Matrix.sum_mul]
      _ = _ := by
        congr 2
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        simp only [Matrix.mul_apply,Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro p _
        rw [mul_comm]

  rw [he,hCD]
  simp only [Matrix.one_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [mul_assoc,hCD,mul_one]
  rw [← mul_assoc,hCD,one_mul]

lemma continuous_tensorTransport : Continuous
    (fun q : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × ConnectionTensor n =>
      tensorTransport q.1.1 q.1.2 q.2) := by
  apply continuous_pi
  intro i
  let P := (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × ConnectionTensor n
  have hC : Continuous (fun q : P => q.1.1) := continuous_fst.comp continuous_fst
  have hD : Continuous (fun q : P => q.1.2) := continuous_snd.comp continuous_fst
  have hT (p : Fin n) : Continuous (fun q : P => q.2 p) := (continuous_apply p).comp continuous_snd
  have hc (p : Fin n) : Continuous (fun q : P => q.1.1 p i) :=
    (continuous_apply i).comp ((continuous_apply p).comp hC)
  exact (hD.matrix_mul (continuous_finsetSum _ (fun p _ => (hc p).smul (hT p)))).matrix_mul hC

lemma boundedFrame_tensor_coercivity (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ boundedFramePairs (n := n) B, ∀ T : ConnectionTensor n,
      δ*‖T‖^2 ≤ tensorSquare (tensorTransport p.1 p.2 T) := by
  apply compact_homogeneous_positive (boundedFramePairs_compact B)
    (fun p T => tensorSquare (tensorTransport p.1 p.2 T))
  · exact (continuous_tensorSquare.comp continuous_tensorTransport).continuousOn
  · intro p hp T hT
    apply tensorSquare_pos
    intro he
    apply hT
    rw [← tensorTransport_undo hp.2.2.1 hp.2.2.2 T,he,tensorTransport_zero]
  · intro p _ r T
    rw [tensorTransport_smul,tensorSquare_smul]

lemma connection_norm_bound_of_frame {K : LocalKaehlerField n} {z : V n}
    (_hz : z ∈ K.domain) {C D : Matrix (Fin n) (Fin n) ℂ}
    (hCD : C*D=1) (hDC : D*C=1) (hN : Cᴴ*K.matrix z*C=1)
    {δ : ℝ} (_hδ : 0 < δ)
    (hc : ∀ T : ConnectionTensor n, δ*‖T‖^2 ≤ tensorSquare (tensorTransport C D T)) :
    δ*‖fun i => K.connection i z‖^2 ≤ K.calabiNorm z := by
  have hC : IsUnit C := ⟨⟨C,D,hCD,hDC⟩,rfl⟩
  have hi : C⁻¹=D := Matrix.inv_eq_right_inv hCD
  have hI : C⁻¹*(K.matrix z)⁻¹*(Cᴴ)⁻¹=1 := by
    rw [← Matrix.mul_inv_rev,← Matrix.mul_inv_rev,← mul_assoc,hN,inv_one]
  have he := tensorPairAt_changeBasis C (K.matrix z)⁻¹ (K.matrix z) hC
    (fun i => K.connection i z) (fun i => K.connection i z)
  rw [hI,hN] at he
  have ht : pullConnectionTensor C (fun i => K.connection i z) =
      tensorTransport C D (fun i => K.connection i z) := by
    unfold pullConnectionTensor tensorTransport
    rw [hi]
  rw [ht] at he
  have hs : tensorSquare (tensorTransport C D (fun i => K.connection i z)) = K.calabiNorm z := by
    change (tensorPairAt 1 1 _ _).re = _
    exact congrArg Complex.re he
  rw [← hs]
  exact hc _
end KaehlerCalculus

end
end

end OAI
