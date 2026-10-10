import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalPotential
import OAI.Combinatorics.KMedian.Geometry.MomentAnalysis

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

structure Actions (I E : Type*) [DecidableEq I] [DecidableEq E] where
  source : E → I
  erase : E → Finset I
  ordinary : Finset E

noncomputable def relevant (D : Actions I E) (S : Finset I) : Finset E :=
  univ.filter (fun e => (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty)

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

noncomputable def physical (D : Actions I E) (S : Finset I) (A : Finset E) : Finset I :=
  S \ A.biUnion D.erase

noncomputable def internal (D : Actions I E) (S : Finset I) (A : Finset E) : Finset E :=
  (A ∩ relevant D S).filter (fun e => e ∈ D.ordinary ∧ D.source e ∈ S)

noncomputable def nextAlive (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : Finset I :=
  if h : (internal D S A).Nonempty then
    retained (coefficient x (mass g S)) (d (D.source h.choose)) d (physical D S A)
  else physical D S A

noncomputable def nextCap (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) : ℝ :=
  (A ∩ D.ordinary).fold min bForce (fun e => d (D.source e))

omit [Fintype E] in
 theorem physical_subset (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A ⊆ S := sdiff_subset

 theorem nextAlive_subset (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAlive D x g d S A ⊆ S := by
  unfold nextAlive
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

theorem physical_restrict (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A = physical D S (A ∩ relevant D S) := by
  ext i
  simp only [physical, mem_sdiff, mem_biUnion]
  constructor
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    exact hnot ⟨e, (mem_inter.mp he).1, hie⟩
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    have hrel : e ∈ relevant D S := (mem_relevant D S e).mpr (Or.inr ⟨i, mem_inter.mpr ⟨hi, hie⟩⟩)
    exact hnot ⟨e, mem_inter.mpr ⟨he, hrel⟩, hie⟩

 theorem nextAlive_zero (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAlive D x g d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAlive, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

 theorem nextAlive_one_external (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E) (ha : A ∩ relevant D S={e})
    (he : ¬(e ∈ D.ordinary ∧ D.source e ∈ S)) :
    nextAlive D x g d S A=S \ D.erase e := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_singleton, he, ite_false]
  simp only [nextAlive, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, singleton_biUnion]

 theorem nextAlive_one_internal (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E) (ha : A ∩ relevant D S={e})
    (he : e ∈ D.ordinary ∧ D.source e ∈ S) :
    nextAlive D x g d S A=
      retained (coefficient x (mass g S)) (d (D.source e)) d (S \ D.erase e) := by
  have hi : internal D S A={e} := by simp [internal, ha, he]
  have hne : (internal D S A).Nonempty := by rw [hi]; exact singleton_nonempty _
  rw [nextAlive, dite_eq_left hne]
  have hchoose : hne.choose=e := by simpa only [hi, mem_singleton] using hne.choose_spec
  rw [hchoose, physical_restrict, ha]
  simp only [physical, singleton_biUnion]

omit [Fintype E] in
 theorem nextCap_le_force (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) :
    nextCap D d bForce A ≤ bForce := (fold_min_le _).mpr (Or.inl le_rfl)

omit [Fintype E] in
 theorem nextCap_nonneg (D : Actions I E) (d : I → ℝ) {bForce : ℝ} (A : Finset E)
    (hb : 0 ≤ bForce) (hd : ∀ e ∈ A ∩ D.ordinary, 0 ≤ d (D.source e)) :
    0 ≤ nextCap D d bForce A := (le_fold_min _).mpr ⟨hb, hd⟩

omit [Fintype E] in
 theorem nextCap_le_selected (D : Actions I E) (d : I → ℝ) {bForce : ℝ} (A : Finset E)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e))
    {e : E} (he : e ∈ A) : nextCap D d bForce A ≤ d (D.source e) := by
  by_cases ho : e ∈ D.ordinary
  · exact (fold_min_le _).mpr (Or.inr ⟨e, mem_inter.mpr ⟨he, ho⟩, le_rfl⟩)
  · exact (nextCap_le_force D d bForce A).trans (hheavy e ho)

noncomputable def charge (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ D.source e ∈ S then
    d (D.source e)-(∑ i ∈ S \ D.erase e, g*max (d (D.source e)-coefficient x (mass g S)*d i) 0)-
      potential x g d S b
  else
    mass g (S ∩ D.erase e)*min b (d (D.source e))-
      coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ D.erase e)-
      B x*mass g (S ∩ D.erase e)*(PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ D.erase e))

 theorem frozen_zero (D : Actions I E) {x g b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E) (hy : mass g S ≤ 1) (hb : bForce ≤ b)
    (ha : A ∩ relevant D S=∅) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤ 0 := by
  rw [nextAlive_zero D x g d S A ha]
  have hcap := (nextCap_le_force D d bForce A).trans hb
  have hm := mul_le_mul_of_nonneg_left hcap (sub_nonneg.mpr hy)
  unfold potential
  linarith only [hm]

theorem frozen_one (D : Actions I E) {x g b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) (hb : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e))
    (ha : A ∩ relevant D S={e}) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤
      charge D x g b d S e := by
  have heA : e ∈ A := inter_subset_left (show e ∈ A ∩ relevant D S by rw [ha]; exact mem_singleton_self _)
  have hcap := nextCap_le_selected D d A hheavy heA
  by_cases he : e ∈ D.ordinary ∧ D.source e ∈ S
  · rw [charge, ite_eq_left he, nextAlive_one_internal D x g d S A e ha he]
    have hc := internal_update_le (x := x) hg hd (sdiff_subset : S \ D.erase e ⊆ S) hy hcap
    rw [← coefficient_eq] at hc
    linarith only [hc]
  · rw [charge, ite_eq_right he, nextAlive_one_external D x g d S A e ha he]
    have hsub : S ∩ D.erase e ⊆ S := inter_subset_left
    have h := external_update_le (x := x) (g := g) (d := d) hsub hy
      ((nextCap_le_force D d bForce A).trans hb)
    have hsd : S \ (S ∩ D.erase e)=S \ D.erase e := by ext i; simp only [mem_sdiff, mem_inter]; tauto
    rw [hsd, ← coefficient_eq] at h
    have hm := mul_le_mul_of_nonneg_left (le_min ((nextCap_le_force D d bForce A).trans hb) hcap)
      (mass_nonneg hg (S ∩ D.erase e))
    linarith only [h, hm]

end MetricKMedian.FixedBatch
end
end

end OAI
