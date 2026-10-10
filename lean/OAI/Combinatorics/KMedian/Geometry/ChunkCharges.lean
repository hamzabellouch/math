import Mathlib
import OAI.Combinatorics.KMedian.Geometry.FixedBatchTransition

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem charge_eq_zero (D : Actions I E) (x g b : ℝ) (d : I → ℝ)
    (S : Finset I) {e : E} (he : e ∉ relevant D S) : charge D x g b d S e=0 := by
  have hn : ¬(e ∈ D.ordinary ∧ D.source e ∈ S) := fun h => he ((mem_relevant D S e).mpr (.inl h))
  have hi : S ∩ D.erase e=∅ := by
    apply not_nonempty_iff_eq_empty.mp
    exact fun h => he ((mem_relevant D S e).mpr (.inr h))
  simp only [charge, ite_eq_right hn, hi, mass, PhysicalPotential.cost, card_empty, Nat.cast_zero, mul_zero,
    sum_empty, zero_mul, sub_zero]

 theorem sum_charge_relevant (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) :
    (∑ e ∈ relevant D S, charge D x g b d S e)=∑ e, charge D x g b d S e := by
  apply sum_subset (subset_univ _)
  intro e _ he
  exact charge_eq_zero D x g b d S he

omit [DecidableEq E] [Fintype E] in
                                                                  
theorem partition_alive_sums (U : Finset E) (erase : E → Finset I) (full S : Finset I)
    (hp : (U : Set E).PairwiseDisjoint erase) (hu : U.biUnion erase=full)
    (g : ℝ) (d : I → ℝ) :
    (∑ e ∈ U, mass g (S ∩ erase e))=mass g (S ∩ full) ∧
    (∑ e ∈ U, PhysicalPotential.cost g d (S ∩ erase e))=PhysicalPotential.cost g d (S ∩ full) := by
  have hp' : (U : Set E).PairwiseDisjoint (fun e => S ∩ erase e) := by
    intro e he f hf hne
    exact (hp he hf hne).mono inter_subset_right inter_subset_right
  have hu' : U.biUnion (fun e => S ∩ erase e)=S ∩ full := by
    rw [← hu]
    ext i
    simp only [mem_biUnion, mem_inter]
    constructor
    · rintro ⟨e, he, hi, hie⟩
      exact ⟨hi, e, he, hie⟩
    · rintro ⟨hi, e, he, hie⟩
      exact ⟨e, he, hi, hie⟩
  constructor
  · simp only [mass, ← mul_sum]
    rw [← Nat.cast_sum, ← card_biUnion hp', hu']
  · exact (hu' ▸ sum_biUnion (f := fun i => g*d i) hp').symm

omit [Fintype E] [Fintype H] in

theorem external_chunks_le (D : Actions I E) (Full : Actions I H)
    (U : Finset E) (h : H) (x g b : ℝ) (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hp : (U : Set E).PairwiseDisjoint D.erase) (hu : U.biUnion D.erase=Full.erase h)
    (hsource : ∀ e ∈ U, D.source e=Full.source h)
    (hext : ∀ e ∈ U, ¬(e ∈ D.ordinary ∧ D.source e ∈ S))
    (hfull : ¬(h ∈ Full.ordinary ∧ Full.source h ∈ S)) :
    (∑ e ∈ U, charge D x g b d S e) ≤ charge Full x g b d S h := by
  have heq : ∀ e ∈ U, charge D x g b d S e=
      mass g (S ∩ D.erase e)*min b (d (Full.source h))-
        coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ D.erase e)-
        B x*mass g (S ∩ D.erase e)*(PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ D.erase e)) := by
    intro e he
    rw [charge, ite_eq_right (hext e he), hsource e he]
  rw [sum_congr rfl heq, charge, ite_eq_right hfull]
  obtain ⟨hm, hc⟩ := partition_alive_sums U D.erase (Full.erase h) S hp hu g d
  have hle := chunks_le_full U (fun e => mass g (S ∩ D.erase e))
    (fun e => PhysicalPotential.cost g d (S ∩ D.erase e))
    (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S) (min b (d (Full.source h)))
    (fun e _ => mass_nonneg hg _) (fun e _ => cost_nonneg hg (fun i hi => hd i (mem_inter.mp hi).1))
    (B_nonneg x)
  simpa only [hm, hc] using hle

theorem split_actions_le (D : Actions I E) (Full : Actions I H) (parent : E → H)
    (x g b : ℝ) (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hp : ∀ h, (↑(univ.filter (fun e => parent e=h)) : Set E).PairwiseDisjoint D.erase)
    (hu : ∀ h, (univ.filter (fun e => parent e=h)).biUnion D.erase=Full.erase h)
    (hsource : ∀ e, D.source e=Full.source (parent e))
    (hinside : ∀ e, (e ∈ D.ordinary ∧ D.source e ∈ S) ↔
      (parent e ∈ Full.ordinary ∧ Full.source (parent e) ∈ S))
    (hsingle : ∀ h, h ∈ Full.ordinary ∧ Full.source h ∈ S →
      ∃ e, univ.filter (fun e => parent e=h)={e}) :
    (∑ e ∈ relevant D S, charge D x g b d S e) ≤
      ∑ h ∈ relevant Full S, charge Full x g b d S h := by
  rw [sum_charge_relevant, sum_charge_relevant, ← sum_fiberwise univ parent]
  apply sum_le_sum
  intro h _
  by_cases hh : h ∈ Full.ordinary ∧ Full.source h ∈ S
  · obtain ⟨e, he⟩ := hsingle h hh
    have hmem : e ∈ univ.filter (fun e => parent e=h) := he ▸ mem_singleton_self e
    have hparent : parent e=h := (mem_filter.mp hmem).2
    have hsrc : D.source e=Full.source h := by rw [hsource, hparent]
    have herase : D.erase e=Full.erase h := by simpa only [he, singleton_biUnion] using hu h
    have hin : e ∈ D.ordinary ∧ D.source e ∈ S := (hinside e).mpr (hparent ▸ hh)
    rw [he, sum_singleton, charge, ite_eq_left hin, charge, ite_eq_left hh, hsrc, herase]
  · apply external_chunks_le D Full _ h x g b d S hg hd (hp h) (hu h)
    · intro e he
      rw [hsource, (mem_filter.mp he).2]
    · intro e he hin
      exact hh ((mem_filter.mp he).2 ▸ (hinside e).mp hin)
    · exact hh

end MetricKMedian.FixedBatch
end
end

end OAI
