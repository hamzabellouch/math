import Mathlib
import OAI.Geometry.PrescribedPotential.CompactHomogeneousBounds
import OAI.Geometry.PrescribedPotential.WirtingerCalculus
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Frame Compact Bounds. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def frameGram (G B : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Bᴴ*G*B).trace.re

def frameResidual (A G : Matrix (Fin n) (Fin n) ℂ)
    (R : V n → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(Bᴴ*A*B*(Bᴴ*G*B)).trace.re + ∑ k, (Bᴴ*R (B*ᵥe k)*B).trace.re

lemma frameGram_pos {G B : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) (hB : B ≠ 0) :
    0 < frameGram G B := by
  obtain ⟨Q,hQ,rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  have hn : Q*B ≠ 0 := by
    intro he
    apply hB
    exact hQ.mul_left_cancel (by simpa using he)
  have he : Bᴴ*(Qᴴ*Q)*B = (Q*B)ᴴ*(Q*B) := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  change 0 < (Bᴴ*(Qᴴ*Q)*B).trace.re
  rw [he]
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (Q*B)).trace_nonneg
  have hne : ((Q*B)ᴴ*(Q*B)).trace ≠ 0 := by
    intro he0
    exact hn ((Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := Q*B)).mp he0)
  exact (Complex.pos_iff.mp (lt_of_le_of_ne hp (Ne.symm hne))).1

lemma frameGram_smul (G B : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    frameGram G (r • B) = r^2*frameGram G B := by
  change frameGram G ((r:ℂ) • B) = _
  unfold frameGram
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.trace_smul,smul_eq_mul,← Complex.ofReal_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma frameResidual_smul (A G : Matrix (Fin n) (Fin n) ℂ)
    (R : V n → Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ r : ℝ, ∀ v, R (r • v) = (r:ℂ)^2 • R v)
    (B : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    frameResidual A G R (r • B) = r^4*frameResidual A G R B := by
  unfold frameResidual
  simp only [Matrix.smul_mulVec,hR]
  change -(((r:ℂ) • B)ᴴ*A*((r:ℂ) • B)*(((r:ℂ) • B)ᴴ*G*((r:ℂ) • B))).trace.re +
    (∑ k, (((r:ℂ) • B)ᴴ*((r:ℂ)^2 • R (B*ᵥe k))*((r:ℂ) • B)).trace.re) = _
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.trace_smul,smul_eq_mul]
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [← Finset.mul_sum]
  ring

lemma continuousOn_trace_re {X : Type*} [TopologicalSpace X] {K : Set X}
    {F : X → Matrix (Fin n) (Fin n) ℂ} (hF : ContinuousOn F K) :
    ContinuousOn (fun x => (F x).trace.re) K := by
  simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  exact continuousOn_finsetSum _ (fun k _ =>
    Complex.continuous_re.comp_continuousOn (continuousOn_pi.mp (continuousOn_pi.mp hF k) k))

lemma continuousOn_matrix_star {X : Type*} [TopologicalSpace X] {K : Set X}
    {F : X → Matrix (Fin n) (Fin n) ℂ} (hF : ContinuousOn F K) :
    ContinuousOn (fun x => (F x)ᴴ) K := by
  exact continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
    (continuousOn_pi.mp (continuousOn_pi.mp hF j) i).star))

lemma compact_frame_bound {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (A G : X → Matrix (Fin n) (Fin n) ℂ) (R : X → V n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ContinuousOn A K) (hG : ContinuousOn G K) (hp : ∀ x ∈ K, (G x).PosDef)
    (hR : ContinuousOn (fun q : X × V n => R q.1 q.2) (K ×ˢ univ))
    (hRh : ∀ x ∈ K, ∀ r : ℝ, ∀ v, R x (r • v) = (r:ℂ)^2 • R x v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ B,
      -C*(frameGram (G x) B)^2 ≤ frameResidual (A x) (G x) (R x) B := by
  let E := Matrix (Fin n) (Fin n) ℂ
  have hcgram : ContinuousOn (fun q : X × E => frameGram (G q.1) q.2) (K ×ˢ univ) := by
    apply continuousOn_trace_re
    exact ((continuousOn_matrix_star continuous_snd.continuousOn).mul
      (hG.comp continuous_fst.continuousOn (fun _ h => h.1))).mul continuous_snd.continuousOn
  have hcres : ContinuousOn (fun q : X × E => frameResidual (A q.1) (G q.1) (R q.1) q.2) (K ×ˢ univ) := by
    have hb := continuous_snd.continuousOn (s := K ×ˢ (univ : Set E))
    have hbs := continuousOn_matrix_star hb
    have ha := hA.comp continuous_fst.continuousOn (s := K ×ˢ (univ : Set E)) (fun _ h => h.1)
    have hg := hG.comp continuous_fst.continuousOn (s := K ×ˢ (univ : Set E)) (fun _ h => h.1)
    apply ContinuousOn.add
    · exact (continuousOn_trace_re (((hbs.mul ha).mul hb).mul ((hbs.mul hg).mul hb))).neg
    · apply continuousOn_finsetSum
      intro k _
      apply continuousOn_trace_re
      apply ContinuousOn.mul (ContinuousOn.mul hbs _) hb
      apply hR.comp (f := fun q : X × E => (q.1,q.2*ᵥe k))
      · exact continuous_fst.continuousOn.prodMk
          (continuous_snd.matrix_mulVec continuous_const).continuousOn
      · intro q hq
        exact ⟨hq.1,mem_univ _⟩
  obtain ⟨δ,hδ,hgram⟩ := compact_homogeneous_positive hK (fun x B => frameGram (G x) B)
    (hcgram.mono (fun _ h => ⟨h.1,mem_univ _⟩))
    (fun x hx B hB => frameGram_pos (hp x hx) hB) (fun x _ r B => frameGram_smul (G x) B r)
  obtain ⟨C,hC,hres⟩ := compact_homogeneous_bound hK 4 (by norm_num)
    (fun x B => frameResidual (A x) (G x) (R x) B)
    (hcres.mono (fun _ h => ⟨h.1,mem_univ _⟩))
    (fun x hx r B => frameResidual_smul _ _ _ (hRh x hx) B r)
  refine ⟨C/δ^2,div_nonneg hC (sq_nonneg δ),?_⟩
  intro x hx B
  have hg := hgram x hx B
  have hr := neg_abs_le (frameResidual (A x) (G x) (R x) B) |>.trans' (neg_le_neg (hres x hx B))
  have hq : 0 ≤ frameGram (G x) B := (mul_nonneg hδ.le (sq_nonneg _)).trans hg
  have hh : δ^2*‖B‖^4 ≤ (frameGram (G x) B)^2 := by
    have hh := sq_le_sq₀ (mul_nonneg hδ.le (sq_nonneg ‖B‖)) hq |>.mpr hg
    simpa only [mul_pow,← pow_mul] using hh
  have hmul := mul_le_mul_of_nonneg_left hh (div_nonneg hC (sq_nonneg δ))
  have he : C/δ^2*(δ^2*‖B‖^4) = C*‖B‖^4 := by field_simp
  rw [he] at hmul
  linarith
end KaehlerCalculus

end
end

end OAI
