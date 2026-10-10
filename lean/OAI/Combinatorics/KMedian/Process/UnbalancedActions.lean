import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalBatchLaw
import OAI.Combinatorics.KMedian.Process.ActualActions
import OAI.Combinatorics.KMedian.Process.QuadraticCount

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def countErase (D : Actions I E) (Δ : ℕ) (e : E) : Finset I :=
  if e ∈ balancedActions D Δ then ∅ else D.erase e

noncomputable def countOpening (D : Actions I E) (Δ : ℕ) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ e ∉ balancedActions D Δ then 1 else 0

omit [Fintype I] [Fintype E] in
 theorem countErase_subset (D : Actions I E) (Δ : ℕ) (e : E) : countErase D Δ e ⊆ D.erase e := by
  unfold countErase
  split_ifs
  · exact empty_subset _
  · exact Subset.rfl

omit [Fintype I] [Fintype E] in
 theorem countOpening_nonneg (D : Actions I E) (Δ : ℕ) (e : E) : 0 ≤ countOpening D Δ e := by
  unfold countOpening
  split_ifs <;> norm_num

omit [Fintype I] in
 theorem masked_union (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (univ.filter (fun e => ω e=true)).biUnion (countErase D Δ)=
      (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω).biUnion D.erase := by
  ext i
  simp only [mem_biUnion,mem_filter,mem_univ,true_and,PhysicalBatchLaw.unbalanced]
  constructor
  · rintro ⟨e,he,hi⟩
    by_cases hb : e ∈ balancedActions D Δ
    · simp only [countErase,ite_eq_left hb,Finset.notMem_empty] at hi
    · exact ⟨e,⟨he,hb⟩,by simpa only [countErase,ite_eq_right hb] using hi⟩
  · rintro ⟨e,⟨he,hb⟩,hi⟩
    exact ⟨e,he,by simpa only [countErase,ite_eq_right hb] using hi⟩

omit [Fintype I] in
 theorem masked_openings (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (∑ e, countOpening D Δ e*CountStatistic.bit ω e)=
    (((PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω) ∩ D.ordinary).card:ℝ) := by
  have heq : (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω ∩ D.ordinary) =
      univ.filter (fun e => ω e=true ∧ e ∉ balancedActions D Δ ∧ e ∈ D.ordinary) := by
    ext e
    simp [PhysicalBatchLaw.unbalanced, and_assoc]
  rw [heq, ← sum_boole]
  apply sum_congr rfl
  intro e _
  simp only [countOpening,CountStatistic.bit]
  split_ifs <;> simp_all

omit [Fintype I] in
 theorem masked_degree (D : Actions I E) (Δ : ℕ)
    (hin : ∀ i, (FiniteGraph.incoming D.erase i).card ≤ Δ) (i : I) :
    (FiniteGraph.incoming (countErase D Δ) i).card ≤ Δ := by
  apply (card_le_card _).trans (hin i)
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,countErase_subset D Δ e (mem_filter.mp he).2⟩

 theorem mass_eq_one_iff {g : ℝ} {Δ n : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) :
    g*(n:ℝ)=1 ↔ n=Δ := by
  rw [← hunit,mul_right_inj' (ne_of_gt hg)]
  exact Nat.cast_inj

 theorem heavy_inl_balanced (Full : Actions I I) (H : Finset I) (Δ : ℕ) {h : I}
    (hh : h ∉ H) : Sum.inl (⟨h,hh⟩ : {i : I // i ∉ H}) ∈
      balancedActions (heavyActions Full H) Δ ↔ (Full.erase h).card=Δ := by
  constructor
  · intro he
    exact (mem_filter.mp he).2
  · intro hc
    apply mem_filter.mpr
    exact ⟨(ordinary_heavyActions Full H _).mpr rfl,hc⟩

 theorem heavy_mass_fiber (Full : Actions I I) (H : Finset I) (g : ℝ) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent Full H e=h),
      mass g ((heavyActions Full H).erase e))=mass g (Full.erase h) := by
  have hh := (partition_alive_sums (univ.filter (fun e => heavyParent Full H e=h))
    (heavyActions Full H).erase (Full.erase h) univ
    (heavy_partition_disjoint Full H h) (heavy_partition_union Full H h) g (fun _ => 0)).1
  simpa only [univ_inter] using hh

theorem masked_mass_fiber (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hH : ∀ h ∈ H, 1 < mass g ((graphActions G).erase h)) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
      mass g (countErase (heavyActions (graphActions G) H) Δ e))=
    if mass g ((graphActions G).erase h)=1 then 0 else mass g ((graphActions G).erase h) := by
  by_cases hh : h ∈ H
  · have hn : mass g ((graphActions G).erase h) ≠ 1 := ne_of_gt (hH h hh)
    rw [ite_eq_right hn,← heavy_mass_fiber (graphActions G) H g h]
    apply sum_congr rfl
    intro e he
    have heh : heavyParent (graphActions G) H e ∈ H := (mem_filter.mp he).2 ▸ hh
    have ho : e ∉ (heavyActions (graphActions G) H).ordinary := by
      rw [ordinary_heavyActions]
      exact (heavyParent_membership _ _ _).mp heh
    have hb : e ∉ balancedActions (heavyActions (graphActions G) H) Δ :=
      fun hb => ho (mem_filter.mp hb).1
    rw [countErase,ite_eq_right hb]
  · rw [heavy_nonheavy_fiber (graphActions G) H hh,sum_singleton]
    have hb : Sum.inl (⟨h,hh⟩ : {i : I // i ∉ H}) ∈
        balancedActions (heavyActions (graphActions G) H) Δ ↔
        mass g ((graphActions G).erase h)=1 := by
      rw [heavy_inl_balanced (graphActions G) H Δ hh]
      exact (mass_eq_one_iff hg hunit).symm
    by_cases hm : mass g ((graphActions G).erase h)=1
    · rw [ite_eq_left hm,countErase,ite_eq_left (hb.mpr hm),mass,card_empty,Nat.cast_zero,mul_zero]
    · rw [ite_eq_right hm,countErase,ite_eq_right (fun he => hm (hb.mp he))]
      rfl

 theorem masked_opening_fiber (G : I → Finset I) (H : Finset I) (Δ : ℕ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1) (h : I) :
    (∑ e ∈ univ.filter (fun e => heavyParent (graphActions G) H e=h),
      countOpening (heavyActions (graphActions G) H) Δ e)=
    if h ∉ H ∧ mass g ((graphActions G).erase h) ≠ 1 then 1 else 0 := by
  by_cases hh : h ∈ H
  · rw [ite_eq_right (fun he => he.1 hh)]
    apply sum_eq_zero
    intro e he
    have heh : heavyParent (graphActions G) H e ∈ H := (mem_filter.mp he).2 ▸ hh
    have ho : e ∉ (heavyActions (graphActions G) H).ordinary := by
      rw [ordinary_heavyActions]
      exact (heavyParent_membership _ _ _).mp heh
    exact ite_eq_right (fun he => ho he.1)
  · rw [heavy_nonheavy_fiber (graphActions G) H hh,sum_singleton]
    simp only [countOpening, ordinary_heavyActions, heavy_inl_balanced (graphActions G) H Δ hh,
      Sum.isLeft_inl, true_and, hh, not_false_eq_true, mass, ne_eq,
      mass_eq_one_iff hg hunit]

end MetricKMedian.FixedBatch
end
end

end OAI
