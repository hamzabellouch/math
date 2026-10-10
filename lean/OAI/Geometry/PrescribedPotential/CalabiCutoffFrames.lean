import Mathlib
import OAI.Geometry.PrescribedPotential.FrameCompactBounds
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.HolomorphicDirection
import OAI.Geometry.PrescribedPotential.ScalarFrameCalculus
import OAI.Geometry.PrescribedPotential.ScalarProductLaplacian

namespace OAI

/-! Calabi Cutoff Frames. -/

section

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma holGradientSquare_sq {f : V n → ℝ} {z : V n} (hf : ContDiffAt ℝ ∞ f z) :
    holGradientSquare (fun y => (f y)^2) z = 4*(f z)^2*holGradientSquare f z := by
  have hfc : ContDiffAt ℝ ∞ (fun y => (f y:ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hd (k : Fin n) : dz (e k) (fun y => ((f y)^2:ℂ)) z = (2*(f z:ℂ))*dz (e k) (fun y => (f y:ℂ)) z := by
    simp only [pow_two]
    change wderiv (-Complex.I) (e k) (fun y => (f y:ℂ)*(f y:ℂ)) z = _
    rw [wderiv_mul (hfc.differentiableAt (by simp)) (hfc.differentiableAt (by simp))]
    change dz (e k) _ z*(f z:ℂ)+(f z:ℂ)*dz (e k) _ z = _
    ring
  rw [holGradientSquare_eq,holGradientSquare_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hco : (fun y => (((f y)^2:ℝ):ℂ)) = (fun y => (f y:ℂ)^2) := by funext y; simp
  rw [hco,hd,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs]
  ring

def frameGradientSquare (f : V n → ℝ) (z : V n) (C : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ k, ‖∑ p, C p k*dz (e p) (fun y => (f y:ℂ)) z‖^2

lemma frameGradientSquare_continuous {f : V n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun q : V n × Matrix (Fin n) (Fin n) ℂ => frameGradientSquare f q.1 q.2) := by
  have hfc : ContDiff ℝ ∞ (fun y => (f y:ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  unfold frameGradientSquare
  apply continuous_finsetSum
  intro k _
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_finsetSum
  intro p _
  exact ((continuous_apply_apply p k).comp continuous_snd).mul
    ((contDiff_iff_contDiffAt.mpr (fun z => wderiv_smooth hfc.contDiffAt _ _)).continuous.comp continuous_fst)

lemma holGradientSquare_linear (B : V n →L[ℂ] V n) {f : V n → ℝ} {w : V n}
    (hf : ContDiffAt ℝ ∞ f (B w)) :
    holGradientSquare (fun y => f (B y)) w = frameGradientSquare f (B w) (frameMatrix B) := by
  have hfc : ContDiffAt ℝ ∞ (fun y => (f y:ℂ)) (B w) := Complex.ofRealCLM.contDiff.contDiffAt.comp (B w) hf
  rw [holGradientSquare_eq]
  unfold frameGradientSquare
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  change wderiv (-Complex.I) (e k) (fun y => (f (B y):ℂ)) w = _
  rw [wderiv_comp_linear B (hfc.differentiableAt (by simp))]
  change dz (B (e k)) (fun y => (f y:ℂ)) (B w) = _
  rw [dz_direction_coordinates]
  rfl

lemma frameGradientSquare_bounded {L : Set (V n)} (hL : IsCompact L) {f : V n → ℝ}
    (hf : ContDiff ℝ ∞ f) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ L, ∀ b : Matrix (Fin n) (Fin n) ℂ, ‖b‖ ≤ B → frameGradientSquare f z b ≤ C := by
  obtain ⟨C,hC⟩ := (hL.prod (isCompact_closedBall (0:Matrix (Fin n) (Fin n) ℂ) B)).exists_bound_of_continuousOn
    (frameGradientSquare_continuous hf).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz b hb
  have hp : (z,b) ∈ L ×ˢ closedBall (0:Matrix (Fin n) (Fin n) ℂ) B :=
    ⟨hz,by simpa only [mem_closedBall,dist_zero_right] using hb⟩
  have hh := hC (z,b) hp
  change ‖frameGradientSquare f z b‖ ≤ C at hh
  rw [Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans (hh.trans (le_max_left _ _))

lemma frameHessianTrace_continuous {f : V n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun q : V n × Matrix (Fin n) (Fin n) ℂ =>
      (q.2ᴴ*PotentialKaehler.potentialMatrix f q.1*q.2).trace.re) := by
  have hH : Continuous (PotentialKaehler.potentialMatrix f) :=
    (contDiff_iff_contDiffAt.mpr (fun z => PotentialKaehler.potentialMatrix_smooth hf.contDiffAt)).continuous
  exact continuousOn_univ.mp (continuousOn_trace_re
    (((continuousOn_matrix_star continuous_snd.continuousOn).mul (hH.comp continuous_fst).continuousOn).mul continuous_snd.continuousOn))

lemma frameHessianTrace_bounded {L : Set (V n)} (hL : IsCompact L) {f : V n → ℝ}
    (hf : ContDiff ℝ ∞ f) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ L, ∀ b : Matrix (Fin n) (Fin n) ℂ, ‖b‖ ≤ B →
      -C ≤ (bᴴ*PotentialKaehler.potentialMatrix f z*b).trace.re := by
  obtain ⟨C,hC⟩ := (hL.prod (isCompact_closedBall (0:Matrix (Fin n) (Fin n) ℂ) B)).exists_bound_of_continuousOn
    (frameHessianTrace_continuous hf).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz b hb
  have hp : (z,b) ∈ L ×ˢ closedBall (0:Matrix (Fin n) (Fin n) ℂ) B :=
    ⟨hz,by simpa only [mem_closedBall,dist_zero_right] using hb⟩
  have hh := hC (z,b) hp
  change ‖(bᴴ*PotentialKaehler.potentialMatrix f z*b).trace.re‖ ≤ C at hh
  rw [Real.norm_eq_abs] at hh
  exact (neg_le_neg (hh.trans (le_max_left _ _))).trans (neg_abs_le _)

lemma cutoff_frame_bounds {L : Set (V n)} (hL : IsCompact L) (χ : V n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : V n →L[ℂ] V n) (w : V n), b w ∈ L → ‖frameMatrix b‖ ≤ B →
      -C ≤ (PotentialKaehler.potentialMatrix (fun y => (χ (b y))^2) w).trace.re ∧
      holGradientSquare (fun y => (χ (b y))^2) w ≤ C*(χ (b w))^2 := by
  obtain ⟨C1,hC1,h1⟩ := frameHessianTrace_bounded hL (hχ.pow 2) B
  obtain ⟨C2,hC2,h2⟩ := frameGradientSquare_bounded hL hχ B
  let C := max C1 (4*C2)
  refine ⟨C,hC1.trans (le_max_left _ _),?_⟩
  intro b w hw hb
  constructor
  · rw [potentialMatrix_linear b (hχ.contDiffAt.pow 2)]
    exact (neg_le_neg (le_max_left C1 (4*C2))).trans (h1 _ hw _ hb)
  · have hs : ContDiffAt ℝ ∞ (fun y => χ (b y)) w := hχ.contDiffAt.comp w (b.restrictScalars ℝ).contDiff.contDiffAt
    rw [holGradientSquare_sq hs,holGradientSquare_linear b hχ.contDiffAt]
    have hh := h2 (b w) hw (frameMatrix b) hb
    have hC : 4*C2 ≤ C := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right (by linarith : 4*frameGradientSquare χ (b w) (frameMatrix b) ≤ C) (sq_nonneg (χ (b w)))
    nlinarith
end KaehlerCalculus

end
end

end OAI
