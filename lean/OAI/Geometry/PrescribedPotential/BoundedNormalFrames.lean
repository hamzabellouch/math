import Mathlib
import OAI.Geometry.PrescribedPotential.FrameCompactBounds

namespace OAI

/-! Bounded Normal Frames. -/

section

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma frameGram_compact_lower {X : Type*} [TopologicalSpace X]
    {L : Set X} (hL : IsCompact L) (G : X → Matrix (Fin n) (Fin n) ℂ)
    (hG : ContinuousOn G L) (hp : ∀ x ∈ L, (G x).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, ∀ B, δ*‖B‖^2 ≤ frameGram (G x) B := by
  apply compact_homogeneous_positive hL (fun x B => frameGram (G x) B)
  · apply continuousOn_trace_re
    exact ((continuousOn_matrix_star continuous_snd.continuousOn).mul
      (hG.comp continuous_fst.continuousOn (fun _ h => h.1))).mul continuous_snd.continuousOn
  · exact fun x hx B hB => frameGram_pos (hp x hx) hB
  · exact fun x _ r B => frameGram_smul (G x) B r

lemma unnormalize_matrix {C D M : Matrix (Fin n) (Fin n) ℂ}
    (hCD : C*D = 1) (hM : Cᴴ*M*C = 1) : M = Dᴴ*D := by
  calc
    M = (C*D)ᴴ*M*(C*D) := by rw [hCD]; simp
    _ = Dᴴ*(Cᴴ*M*C)*D := by simp only [Matrix.conjTranspose_mul,mul_assoc]
    _ = Dᴴ*D := by rw [hM,mul_one]

lemma normalizing_frame_gram_le {C G M : Matrix (Fin n) (Fin n) ℂ}
    {R : ℝ} (h : ((R:ℂ) • M-G).PosSemidef) (hNorm : Cᴴ*M*C = 1) :
    frameGram G C ≤ R*n := by
  have hh := (Complex.nonneg_iff.mp (h.conjTranspose_mul_mul_same C).trace_nonneg).1
  rw [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,hNorm,Matrix.trace_sub,Matrix.trace_smul] at hh
  simpa only [Complex.sub_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Matrix.trace_one,Fintype.card_fin,Complex.natCast_re,sub_nonneg,frameGram] using hh

lemma metric_trace_le {G M : Matrix (Fin n) (Fin n) ℂ} {K : ℝ}
    (h : ((K:ℂ) • G-M).PosSemidef) : M.trace.re ≤ K*G.trace.re := by
  have hh := (Complex.nonneg_iff.mp h.trace_nonneg).1
  rw [Matrix.trace_sub,Matrix.trace_smul] at hh
  simpa only [Complex.sub_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,sub_nonneg] using hh

lemma compact_normalizing_frames {X : Type*} [TopologicalSpace X]
    {L : Set X} (hL : IsCompact L) (G : X → Matrix (Fin n) (Fin n) ℂ)
    (hG : ContinuousOn G L) (hp : ∀ x ∈ L, (G x).PosDef)
    {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ L, ∀ M C D : Matrix (Fin n) (Fin n) ℂ,
      ((R:ℂ) • M-G x).PosSemidef → ((K:ℂ) • G x-M).PosSemidef →
      C*D = 1 → Cᴴ*M*C = 1 → ‖C‖ ≤ B ∧ ‖D‖ ≤ B := by
  obtain ⟨a,ha,hGa⟩ := frameGram_compact_lower hL G hG hp
  obtain ⟨b,hb,hIb⟩ := frameGram_compact_lower (n := n)
    (X := Unit) (L := univ) isCompact_univ (fun _ => 1) continuousOn_const (fun _ _ => Matrix.PosDef.one)
  obtain ⟨T,hT⟩ := hL.exists_bound_of_continuousOn (continuousOn_trace_re hG)
  let Tc := max T 0
  let B := max (R*n/a+1) (K*Tc/b+1)
  have htc : 0 ≤ Tc := le_max_right _ _
  refine ⟨B,?_,?_⟩
  · exact (by dsimp [B]; exact (by positivity : 0 ≤ R*n/a+1).trans (le_max_left _ _))
  intro x hx M C D hlow hupp hCD hNorm
  have htr : (G x).trace.re ≤ Tc := by
    exact (le_abs_self _).trans ((hT x hx).trans (le_max_left _ _))
  have hc := (hGa x hx C).trans (normalizing_frame_gram_le hlow hNorm)
  have hc2 : ‖C‖^2 ≤ R*n/a := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hc)
  have hc1 : ‖C‖ ≤ R*n/a+1 := by nlinarith [sq_nonneg (‖C‖-1)]
  have hd := hIb () (mem_univ _) D
  have hDgram : frameGram 1 D = M.trace.re := by
    rw [unnormalize_matrix hCD hNorm]
    simp only [frameGram,mul_one]
  rw [hDgram] at hd
  have hd2 : ‖D‖^2 ≤ K*Tc/b := (le_div_iff₀ hb).mpr (by
    have hm := (metric_trace_le hupp).trans (mul_le_mul_of_nonneg_left htr hK)
    exact (by simpa only [mul_comm] using hd.trans hm))
  have hd1 : ‖D‖ ≤ K*Tc/b+1 := by nlinarith [sq_nonneg (‖D‖-1)]
  exact ⟨hc1.trans (le_max_left _ _),hd1.trans (le_max_right _ _)⟩

def boundedFramePairs (B : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  {p | ‖p.1‖ ≤ B ∧ ‖p.2‖ ≤ B ∧ p.1*p.2 = 1 ∧ p.2*p.1 = 1}

lemma boundedFramePairs_compact (B : ℝ) : IsCompact (boundedFramePairs (n := n) B) := by
  have he : boundedFramePairs (n := n) B =
      (closedBall (0:Matrix (Fin n) (Fin n) ℂ) B ×ˢ closedBall 0 B) ∩
        {p | p.1*p.2 = 1 ∧ p.2*p.1 = 1} := by
    ext p
    simp only [boundedFramePairs,mem_ofPred_eq,mem_inter_iff,mem_prod,mem_closedBall,dist_zero_right]
    tauto
  rw [he]
  apply (isCompact_closedBall _ _ |>.prod (isCompact_closedBall _ _)).inter_right
  have hc : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1*p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hd : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.2*p.1) :=
    continuous_snd.matrix_mul continuous_fst
  exact (isClosed_eq hc continuous_const).inter (isClosed_eq hd continuous_const)

lemma boundedFramePairs_units {B : ℝ} {p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ}
    (hp : p ∈ boundedFramePairs B) : IsUnit p.1 ∧ IsUnit p.2 := by
  exact ⟨⟨⟨p.1,p.2,hp.2.2.1,hp.2.2.2⟩,rfl⟩,⟨⟨p.2,p.1,hp.2.2.2,hp.2.2.1⟩,rfl⟩⟩
end KaehlerCalculus

end
end

end OAI
