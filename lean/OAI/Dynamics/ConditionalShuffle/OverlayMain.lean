import OAI.Dynamics.ConditionalShuffle.ScheduledTransport

namespace OAI

noncomputable section
open scoped Classical
open Filter Topology
namespace Revealed.Overlay
open Thorp Thorp.Conditional Revealed.Split Revealed.Instrument Revealed.Scheduled Thorp.Specht

lemma dimension_size_core (d : ℕ) (hd : 16 ≤ d) : 256*(d+7) ≤ 2^(d+6) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
      rw [show d+1+6 = (d+6)+1 by omega, pow_succ]
      omega

lemma dimension_size_bound (d : ℕ) (hd : 16 ≤ d) :
    256*(d+1+2+4) ≤ Fintype.card (Position (d+1+2+3)) := by
  rw [card_position]
  simpa only [Nat.add_assoc] using dimension_size_core d hd

lemma call_bound {ι : Type} [Fintype ι] (d : ℕ) (hd : 16 ≤ d)
    (hR : (permutationFamily (Position d)).reciprocalSum ≤ 3)
    (L : Sum ι (Position (d+1+2)) ≃ Position (d+1+2+3)) :
    expectedTV (d+1+2+2) L (isActive (d+1+2+3)) (65536*21*(d+1+2+3)) ≤ groupRate d := by
  let g := d+1+2
  let e := Split.outside L
  have h₀ := expectedTV_instrument (d+1+2+2) L (isActive (d+1+2+3)) (65536*21*(d+1+2+3))
  have ht : segmentLength g*8 ≤ 65536*21*(g+3) := by
    unfold segmentLength
    rw [Hybrid.periodLength_eq]
    omega
  have h₁ := Instrument.distance_antitone (stepInstrument (g+3) (isActive (g+3))) (0,e) ht
  have h₂ := distance_schedule_le (g+3) (segmentLength g*8) (isActive (g+3)) (selectedSchedule g)
    (fun i hi => selected_active g i.val hi) e
  have h₃ := distance_periodic (g+3) (segmentLength g) (selectedSchedule g) (selected_periodic g) e 8
  rw [interval_congr _ _ (selectedSchedule g) (segmentSchedule g) (selected_segment g)] at h₃
  have h₄ := group_distance_bound d (by omega) hR (dimension_size_bound d hd) e
  have hh := h₁.trans (h₂.trans (h₃.le.trans h₄))
  exact h₀.le.trans (Instrument.distance_le_changeFintype _ _ _ _ _ hh)

lemma expectedTV_nonneg {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool) (t : ℕ) :
    0 ≤ expectedTV d L σ t := by
  unfold expectedTV tv
  exact mean_nonneg (fun _ => by positivity)

lemma worstCallTV_nonneg (d : ℕ) : 0 ≤ worstCallTV d := by
  unfold worstCallTV
  exact (expectedTV_nonneg _ _ _ _).trans
    (Finset.le_sup' (fun g₀ : State (d+3) => expectedTV (d+2) ((standardLayout d).trans g₀)
      (isActive (d+3)) (65536*21*(d+3))) (Finset.mem_univ (1 : State (d+3))))

lemma worstCallTV_bound (d : ℕ) (hd : 16 ≤ d)
    (hR : (permutationFamily (Position d)).reciprocalSum ≤ 3) :
    worstCallTV (d+1+2) ≤ groupRate d := by
  apply Finset.sup'_le
  intro g₀ _
  exact call_bound d hd hR ((standardLayout (d+1+2)).trans g₀)

theorem overlay_call : Tendsto worstCallTV atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  apply squeeze_zero' (Eventually.of_forall (fun d => worstCallTV_nonneg (d+3)))
    ?_ groupRate_tendsto
  filter_upwards [Thorp.Block.reciprocal_atMost_three, eventually_ge_atTop 16] with d hR hd
  exact worstCallTV_bound d hd hR

end Revealed.Overlay

end

end OAI
