import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedNormalFrames
import OAI.Geometry.PrescribedPotential.CalabiRescue
import OAI.Geometry.PrescribedPotential.CalabiResidualBound

namespace OAI

/-! Calabi Ricci Frames. -/

section

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def frameRicciJet (J : ConnectionTensor n) (C : Matrix (Fin n) (Fin n) ℂ) : ConnectionTensor n :=
  fun i => Cᴴ*(∑ p, C p i • J p)*C

lemma frameRicciJet_continuous : Continuous
    (fun q : ConnectionTensor n × Matrix (Fin n) (Fin n) ℂ => frameRicciJet q.1 q.2) := by
  apply continuous_pi
  intro i
  apply Continuous.matrix_mul _ continuous_snd
  apply Continuous.matrix_mul (continuousOn_univ.mp (continuousOn_matrix_star continuous_snd.continuousOn))
  apply continuous_finsetSum
  intro p _
  exact ((continuous_apply_apply p i).comp continuous_snd).smul ((continuous_apply p).comp continuous_fst)

lemma frameRicci_continuousOn {X : Type*} [TopologicalSpace X] {L : Set X}
    (H : X → Matrix (Fin n) (Fin n) ℂ) (hH : ContinuousOn H L) (B : ℝ) :
    ContinuousOn (fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) =>
      q.2.1ᴴ*H q.1*q.2.1) (L ×ˢ boundedFramePairs B) := by
  have hc : Continuous (fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) => q.2.1) :=
    continuous_fst.comp continuous_snd
  exact ((continuousOn_matrix_star hc.continuousOn).mul
    (hH.comp continuous_fst.continuousOn (fun _ h => h.1))).mul hc.continuousOn

lemma frameRicciJet_continuousOn {X : Type*} [TopologicalSpace X] {L : Set X}
    (J : X → ConnectionTensor n) (hJ : ContinuousOn J L) (B : ℝ) :
    ContinuousOn (fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) =>
      frameRicciJet (J q.1) q.2.1) (L ×ˢ boundedFramePairs B) := by
  apply frameRicciJet_continuous.comp_continuousOn
    (f := fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) => (J q.1,q.2.1))
  exact (hJ.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk
    (continuous_fst.comp continuous_snd).continuousOn

lemma frameRicciTrace_continuousOn {X : Type*} [TopologicalSpace X] {L : Set X}
    (H : X → Matrix (Fin n) (Fin n) ℂ) (hH : ContinuousOn H L) (B : ℝ) :
    ContinuousOn (fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) =>
      (q.2.2ᴴ*(q.2.1ᴴ*H q.1*q.2.1)*q.2.2).trace.re) (L ×ˢ boundedFramePairs B) := by
  have hc : Continuous (fun q : X × (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) => q.2.2) :=
    continuous_snd.comp continuous_snd
  exact continuousOn_trace_re (((continuousOn_matrix_star hc.continuousOn).mul
    (frameRicci_continuousOn H hH B)).mul hc.continuousOn)

lemma calabi_frame_uniform {X : Type*} [TopologicalSpace X] {L : Set X} (hL : IsCompact L)
    (H : X → Matrix (Fin n) (Fin n) ℂ) (J : X → ConnectionTensor n)
    (hH : ContinuousOn H L) (hJ : ContinuousOn J L) (B : ℝ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x ∈ L,
      ∀ p ∈ boundedFramePairs (n := n) B, ∀ T : ConnectionTensor n,
      -C*(1+tensorSquare T) ≤ calabiResidual (p.1ᴴ*H x*p.1) (frameRicciJet (J x) p.1) T ∧
      -C ≤ (p.2ᴴ*(p.1ᴴ*H x*p.1)*p.2).trace.re ∧
      δ*tensorSquare T ≤ rescueSquare p.2 T := by
  let E := Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
  let Q := L ×ˢ boundedFramePairs (n := n) B
  have hQ : IsCompact Q := hL.prod (boundedFramePairs_compact B)
  let H' : X × E → Matrix (Fin n) (Fin n) ℂ := fun q => q.2.1ᴴ*H q.1*q.2.1
  let J' : X × E → ConnectionTensor n := fun q => frameRicciJet (J q.1) q.2.1
  have hh : ContinuousOn H' Q := frameRicci_continuousOn H hH B
  have hj : ContinuousOn J' Q := frameRicciJet_continuousOn J hJ B
  obtain ⟨C1,hC1p,hres⟩ := calabiResidual_compact_bound hQ H' J' hh hj
  have ht : ContinuousOn (fun q : X × E => (q.2.2ᴴ*H' q*q.2.2).trace.re) Q :=
    frameRicciTrace_continuousOn H hH B
  obtain ⟨C2,htrace⟩ := hQ.exists_bound_of_continuousOn ht
  obtain ⟨δ,hδ,hresc⟩ := rescueSquare_compact_lower (boundedFramePairs_compact (n := n) B)
    Prod.snd continuous_snd.continuousOn (fun p hp => (boundedFramePairs_units hp).2)
  let C := max C1 C2
  refine ⟨C,δ,hC1p.trans (le_max_left _ _),hδ,?_⟩
  intro x hx p hp T
  have hq : (x,p) ∈ Q := ⟨hx,hp⟩
  refine ⟨?_,?_,hresc p hp T⟩
  · have hh := hres (x,p) hq T
    have hr := (neg_le_neg hh).trans (neg_abs_le (calabiResidual (H' (x,p)) (J' (x,p)) T))
    have he := (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left C1 C2) (add_nonneg zero_le_one (tensorSquare_nonneg T)))).trans hr
    simpa only [neg_mul,C,H',J'] using he
  · exact (neg_le_neg ((htrace (x,p) hq).trans (le_max_right C1 C2))).trans (neg_abs_le _)
end KaehlerCalculus

end
end

end OAI
