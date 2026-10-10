import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationRegularity

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma lower_pair {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤(11/10)*R) :
    propagationBarrier B R x≤Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x := by
  have Hold := propagation_old_lower_overlap d.B_pos d.r_pos d.R_eq d.l1_le_gamma hx hx'
    (d.old_caps x (d.old_le_new.trans hx)).1
  have H' := Hold.trans (le_propagationPairOffset bad R l1 l2 u H x)
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [H',he]

lemma inner_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x) Z {x | ‖x‖<(27/25)*R}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x)) := by
  have hh : (27/25)*R≤2*L*R := by nlinarith only [mul_pos (show 0<2*L-27/25 by linarith only [d.L_large]) d.R_pos]
  have Hmax := d.finite_step (U:={x | ‖x‖<(27/25)*R}) (propagationInnerIndices bad)
    (zero_mem_propagationInnerIndices bad) (one_mem_propagationInnerIndices bad)
    (fun hi => False.elim (two_not_mem_propagationInnerIndices bad hi))
    (isOpen_lt continuous_norm continuous_const) (fun x hx => hx.le.trans hh)
    (fun x hx hxR => by
      rw [propagationInner_sup]
      exact d.lower_pair hxR (by
        change ‖x‖ < (27/25)*R at hx
        linarith only [hx,d.R_pos]))
  simpa only [propagationInner_sup] using Hmax

lemma middle_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x)) Z
    {x | (26/25)*R<‖x‖ ∧ ‖x‖<2*L*R}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x))) := by
  have Hmax := d.finite_step (U:={x | (26/25)*R<‖x‖ ∧ ‖x‖<2*L*R}) (propagationMiddleIndices bad)
    (zero_mem_propagationMiddleIndices bad) (one_mem_propagationMiddleIndices bad)
    (fun hi x hx => by linarith only [hx.1,d.R_pos])
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
    (fun x hx => hx.2.le) (fun x hx hxR => by
      rw [propagationMiddle_sup]
      have H := le_max_right (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x)
      have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hxR
      linarith only [H,he])
  simpa only [propagationMiddle_sup] using Hmax

lemma outer_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z {x | L*R<‖x‖}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationBarrierOffset B R Z x)) := by
  have hsub : {x : Position | L*R<‖x‖}⊆{x | R<‖x‖} := by
    intro x hx
    have hh : R<L*R := by nlinarith only [mul_pos (show 0<L-1 by linarith only [d.L_large]) d.R_pos]
    exact hh.trans hx
  have hbc := propagationBarrierOffset_continuous B Z d.R_pos
  have Hbar : WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z {x | L*R<‖x‖}
      (cutoffReaction R (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x)) := by
    apply ((propagationBarrier_weak (Z:=Z) d.B_pos d.R_pos d.barrier_small).mono_domain hsub).congr_on (fun x hx => rfl)
    intro x hx
    have hRx : R ≤ ‖x‖ := le_of_lt (hsub hx)
    simp [cutoffReaction,hRx,propagationBarrierOffset_eq hRx]
  apply (weakNuclearSubsolution_offset_iff hbc).2
  apply ((weakNuclearSubsolution_offset_iff hbc).1 Hbar).mono_source_on
    (cutoffReaction_offset_locallyIntegrable d.R_pos hbc)
    (propagationRHS_locallyIntegrable d.R_pos hbc d.mu_measurable d.step_error_measurable d.mu_bounds d.step_error_bounds)
  exact Eventually.of_forall (fun x hx => by
    have hRx : R ≤ ‖x‖ := le_of_lt (hsub hx)
    simpa [cutoffReaction,hRx] using
      (propagation_barrier_source (bad:=bad) (r:=r) (v:=Z*coulombKernel x+propagationBarrierOffset B R Z x)
        hRx (d.mu_nonneg x) (d.p_nonneg x)))

theorem next_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x) Z univ
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x)) := by
  obtain ⟨hlo,hup⟩ := propagation_splice_overlaps d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg
    d.l2_le_l1 d.l1_le_gamma d.upper_overlap d.old_caps d.physical_cap
  apply WeakNuclearSubsolution.radialMaxSplice
    (a:=(27/25)*R) (b:=(26/25)*R) (e:=L*R) (c:=2*L*R)
    (q:=fun x v => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x)) (Z*coulombKernel x+v))
  · linarith only [d.R_pos]
  · linarith only [d.R_pos]
  · nlinarith only [mul_pos (show 0<L-27/25 by linarith only [d.L_large]) d.R_pos]
  · nlinarith only [mul_pos d.L_pos d.R_pos]
  · nlinarith only [mul_pos d.L_pos d.R_pos]
  · exact propagationPairOffset_continuous bad R l1 l2 d.u_cont d.H_cont
  · exact propagationBarrierOffset_continuous B Z d.R_pos
  · exact hlo
  · exact hup
  · exact propagationRHS_locallyIntegrable d.R_pos d.next_continuous d.mu_measurable d.step_error_measurable d.mu_bounds d.step_error_bounds
  · exact d.inner_weak
  · exact d.middle_weak
  · exact d.outer_weak

end PropagationStepHypotheses
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma pair_cap {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R) :
    Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x≤C/‖x‖^4 := by
  have h1 : 0≤l1/R^4 := div_nonneg (d.l2_nonneg.trans d.l2_le_l1) (pow_pos d.R_pos 4).le
  have h2 : 0≤l2/R^4 := div_nonneg d.l2_nonneg (pow_pos d.R_pos 4).le
  have hu := (d.old_caps x (d.old_le_new.trans hx)).2
  by_cases hb : bad
  · simp only [propagationPairOffset,ite_eq_left hb]
    linarith only [hu,h1]
  · have hH := d.physical_cap hb x (d.old_le_new.trans hx) hx'
    simp only [propagationPairOffset,ite_eq_right hb]
    rw [add_max]
    exact max_le (by linarith only [hu,h1]) (by linarith only [hH,h2])

lemma next_caps {x : Position} (hx : R≤‖x‖) :
    propagationBarrier B R x≤Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x ∧
    Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x≤C/‖x‖^4 := by
  have hp := (propagationBarrier_two_sided d.B_pos.le d.R_pos hx).2
  have hbc : propagationBarrier B R x≤C/‖x‖^4 := hp.trans
    (div_le_div_of_nonneg_right d.cap_large (pow_nonneg (norm_nonneg x) 4))
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  unfold propagationNextOffset radialMaxSplice
  split_ifs with ha hb
  · have hx' : ‖x‖≤(11/10)*R := by linarith only [ha,d.R_pos]
    exact ⟨d.lower_pair hx hx',d.pair_cap hx (by
      have H := mul_pos (show 0<2*L-11/10 by linarith only [d.L_large]) d.R_pos
      nlinarith only [hx',H])⟩
  · rw [add_max]
    exact ⟨he ▸ le_max_right _ _, max_le (d.pair_cap hx (by
      have H := mul_pos d.L_pos d.R_pos
      nlinarith only [hb,H])) (by rwa [he])⟩
  · rw [he]
    exact ⟨le_rfl,hbc⟩

lemma next_outer {x : Position} (hx : L*R<‖x‖) :
    Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x=propagationBarrier B R x := by
  obtain ⟨_,hup⟩ := propagation_splice_overlaps d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg
    d.l2_le_l1 d.l1_le_gamma d.upper_overlap d.old_caps d.physical_cap
  have hα : (53/50)*R≤L*R := by
    have H := mul_pos (show 0<L-53/50 by linarith only [d.L_large]) d.R_pos
    nlinarith only [H]
  have hβ : (3/2)*L*R≤2*L*R := by nlinarith only [mul_pos d.L_pos d.R_pos]
  have hRx : R≤‖x‖ := by
    have H := mul_pos (show 0<L-1 by linarith only [d.L_large]) d.R_pos
    nlinarith only [hx,H]
  rw [propagationNextOffset,radialMaxSplice_outer hα hβ hup hx]
  exact propagationBarrierOffset_eq hRx

lemma next_error_nonneg (x : Position) :
    0≤propagationStepError bad r R ‖x‖ (μ x) (p x) :=
  propagationStepError_nonneg (d.mu_nonneg x) (d.p_nonneg x)

lemma next_error_support (hs : ∀ x,r≤‖x‖ → p x=0) :
    ∀ x,R≤‖x‖ → propagationStepError bad r R ‖x‖ (μ x) (p x)=0 := by
  intro x hx
  simp [propagationStepError,not_lt_of_ge hx,hs x (d.old_le_new.trans hx)]

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
