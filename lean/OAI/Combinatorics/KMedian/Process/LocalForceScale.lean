import Mathlib
import OAI.Combinatorics.KMedian.Geometry.TimeAdvance
import OAI.Combinatorics.KMedian.Process.FrozenBatchBound

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Finset Analytic
variable {I : Type*} [DecidableEq I]

theorem local_cap_scale {g b R : ℝ} {d : I → ℝ} {S S₀ : Finset I}
    (hg : 0 < g) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd : ∀ i ∈ S₀, 0 ≤ d i) (hb : 0 ≤ b) (hbR : b ≤ 5*R)
    (hR : ∃ i ∈ S₀, R=d i) :
    b ≤ 5*(cost g d S+(1-mass g S)*b)/g := by
  let Q := cost g d S+(1-mass g S)*b
  have hy : mass g S ≤ 1 := (mass_mono hg.le hS).trans_eq hm₀
  have hV0 := cost_nonneg hg.le (fun i hi => hd i (hS hi))
  have hVQ : cost g d S ≤ Q := le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hy) hb)
  have hQ : 0 ≤ Q := hV0.trans hVQ
  change b ≤ 5*Q/g
  apply (le_div_iff₀ hg).mpr
  by_cases heq : S=S₀
  · obtain ⟨i, hi, hRi⟩ := hR
    have hp := point_cost_le hg.le (fun i hi => hd i (hS hi)) (heq.symm ▸ hi)
    rw [← hRi] at hp
    have hm := mul_le_mul_of_nonneg_right hbR hg.le
    nlinarith only [hp, hm, hVQ]
  · have hc : S.card < S₀.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS, heq⟩)
    have hc' : (S.card:ℝ)+1 ≤ (S₀.card:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hc)
    have hmul := mul_le_mul_of_nonneg_left hc' hg.le
    have hgap : g ≤ 1-mass g S := by
      unfold mass at hm₀ ⊢
      nlinarith only [hmul, hm₀]
    have hb' := mul_le_mul_of_nonneg_right hgap hb
    dsimp only [Q] at hQ ⊢
    nlinarith only [hb', hV0, hQ]

omit [DecidableEq I] in
 theorem local_point_scale {g b : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 < g) (hd : ∀ i ∈ S, 0 ≤ d i) (hb : 0 ≤ b) (hy : mass g S ≤ 1) :
    ∀ i ∈ S, d i ≤ (cost g d S+(1-mass g S)*b)/g := by
  intro i hi
  apply (le_div_iff₀ hg).mpr
  have hp := point_cost_le hg.le hd hi
  have hmiss := mul_nonneg (sub_nonneg.mpr hy) hb
  nlinarith only [hp, hmiss]

end MetricKMedian.PhysicalPotential

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem relevant_mono (D : Actions I E) {S T : Finset I} (hS : S ⊆ T) :
    relevant D S ⊆ relevant D T := by
  intro e he
  rw [mem_relevant] at he ⊢
  rcases he with he | ⟨i, hi⟩
  · exact Or.inl ⟨he.1, hS he.2⟩
  · exact Or.inr ⟨i, mem_inter.mpr ⟨hS (mem_inter.mp hi).1, (mem_inter.mp hi).2⟩⟩

theorem ideal_local_lower (D : Actions I E) {x g b Q : ℝ}
    (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 < g) (hQ : 0 ≤ Q)
    (hd0 : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ S, d i ≤ Q/g)
    (hy : mass g S ≤ 1) (hVQ : PhysicalPotential.cost g d S ≤ Q)
    (hb0 : 0 ≤ b) (hbQ : b ≤ 5*(Q/g)) :
    -(8*((relevant D S).card:ℝ)+2)*Q ≤
      timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant D S, charge D x g b d S e) := by
  have hc : ∀ e ∈ relevant D S, -(8*(Q/g)) ≤ charge D x g b d S e := by
    intro e _
    exact (abs_le.mp (charge_bound D d S hx0 hx1 hg.le (div_nonneg hQ hg.le)
      hd0 hdQ hy hb0 hbQ e)).1
  have hs := sum_le_sum hc
  simp only [sum_const, nsmul_eq_mul] at hs
  have hg' := mul_le_mul_of_nonneg_left hs hg.le
  have he : g*(((relevant D S).card:ℝ)* -(8*(Q/g)))=
      -(8*((relevant D S).card:ℝ)*Q) := by field_simp
  rw [he] at hg'
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg.le S) hy)).1
  have hV0 : 0 ≤ PhysicalPotential.cost g d S := cost_nonneg hg.le (fun i _ => hd0 i)
  have ht := mul_le_mul_of_nonneg_right hr hV0
  nlinarith only [hg', ht, hVQ]

end MetricKMedian.FixedBatch
end
end

end OAI
