import Mathlib
import OAI.Combinatorics.KMedian.Process.ForceBatchBound
import OAI.Combinatorics.KMedian.Process.LocalForceScale

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem forced_step_local_bound (D : Actions I E) (Full : Actions I H)
    (μ : FiniteLaw (Finset E)) {x g h b b' : ℝ} {N : ℕ}
    (d : I → ℝ) (S F : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hsmall : (16*(N:ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hδ : g ≤ mass g F)
    (hd0 : ∀ i, 0 ≤ d i) (hb0 : 0 ≤ b)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb'0 : 0 ≤ b') (hb' : b' ≤ b) (hbF : ∀ i ∈ F, b' ≤ d i)
    (hD : (relevant D S).card ≤ N) (hFull : (relevant Full S).card ≤ N)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant Full S, charge Full x g b d S e)) := by
  let V := PhysicalPotential.cost g d S
  let Q := V+(1-mass g S)*b
  have hV : 0 ≤ V := cost_nonneg hg0.le (fun i _ => hd0 i)
  have hVQ : V ≤ Q := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hy) hb0)
  have hQ : 0 ≤ Q := hV.trans hVQ
  have hFne : F.Nonempty := by
    by_contra hne
    have he : F=∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [he, mass, card_empty, Nat.cast_zero, mul_zero] at hδ
    exact not_lt_of_ge hδ hg0
  have hcap := force_cap_bound hg0 (fun i _ => hd0 i) hF hFne hbF
  have hsaving := force_fraction hx1 hg0 (fun i _ => hd0 i) hF hδ hy hb'0 hb' hbF
  change savingsFraction g*Q ≤ potential x g d S b-potential x g d (S \ F) b' at hsaving
  have hpost := post_force_bound D μ (coefficient x (mass g S)) d (S \ F)
    hx0 hx1 hg0 hg1 hh0 hh1 hV (fun i _ => hd0 i)
    ((mass_mono hg0.le sdiff_subset).trans hy)
    (cost_mono hg0.le (fun i _ => hd0 i) sdiff_subset) hb'0 hcap
    (fun A => nextCap_nonneg D d A hb'0 (fun e _ => hd0 _))
    (fun e he => hmarg e (relevant_mono D sdiff_subset he))
  have hcard : ((relevant D (S \ F)).card:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (card_le_card (relevant_mono D sdiff_subset)).trans hD
  have hpostM : (8*((relevant D (S \ F)).card:ℝ)+8)*h*V ≤ (8*(N:ℝ)+8)*h*Q := by
    have hc := mul_le_mul_of_nonneg_right (show 8*((relevant D (S \ F)).card:ℝ)+8 ≤ 8*(N:ℝ)+8 by
      linarith only [hcard]) hh0
    exact mul_le_mul hc hVQ hV (by positivity)
  have hpoint : ∀ i ∈ S, d i ≤ Q/g := local_point_scale hg0 (fun i _ => hd0 i) hb0 hy
  have hJ := ideal_local_lower Full d S hx0 hx1 hg0 hQ hd0 hpoint hy hVQ hb0 hbQ
  have hfcard : ((relevant Full S).card:ℝ) ≤ (N:ℝ) := by exact_mod_cast hFull
  have hJM : -(8*(N:ℝ)+2)*Q ≤
      timeRate x (mass g S)*V+g*(∑ e ∈ relevant Full S, charge Full x g b d S e) := by
    apply le_trans _ hJ
    exact mul_le_mul_of_nonneg_right (by linarith only [hfcard]) hQ
  have htarget := mul_le_mul_of_nonneg_left hJM hh0
  have hsmallQ := mul_le_mul_of_nonneg_right hsmall hQ
  rw [μ.expect_sub, μ.expect_const] at hpost ⊢
  change μ.expect _-potential x g d S b ≤
    h*(timeRate x (mass g S)*V+g*(∑ e ∈ relevant Full S, charge Full x g b d S e))
  nlinarith only [hpost, hpostM, hsaving, htarget, hsmallQ]

end MetricKMedian.FixedBatch
end
end

end OAI
