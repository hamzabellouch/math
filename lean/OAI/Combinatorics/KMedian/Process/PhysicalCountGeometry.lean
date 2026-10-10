import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyRound
import OAI.Combinatorics.KMedian.Process.CountGeometry
import OAI.Combinatorics.KMedian.Process.UnbalancedActions

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem balanced_disjoint (D : Actions I E) (Δ : ℕ) (ω : E → Bool) :
    (↑(PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω) : Set E).PairwiseDisjoint D.erase := by
  intro e he f hf hne
  have he' := mem_inter.mp he
  have hf' := mem_inter.mp hf
  apply disjoint_left.mpr
  intro i hi hj
  have hconf : f ∈ balancedConflicts D Δ e := by
    rw [balancedConflicts,ite_eq_left he'.2]
    unfold FiniteGraph.conflicts
    apply mem_erase.mpr
    refine ⟨Ne.symm hne,mem_inter.mpr ⟨?_,hf'.2⟩⟩
    exact (FiniteGraph.mem_touching D.erase (D.erase e) f).mpr ⟨i,hi,hj⟩
  have ht := (mem_filter.mp he'.1).2.2 f hconf
  have hu := (mem_filter.mp hf'.1).2.1
  simp only [ht,Bool.false_eq_true] at hu

 theorem balanced_mass (D : Actions I E) (Δ : ℕ) (ω : E → Bool) {g : ℝ}
    (hunit : g*(Δ:ℝ)=1) :
    mass g ((PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).biUnion D.erase)=
      ((PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).card:ℝ) := by
  rw [mass,card_biUnion (balanced_disjoint D Δ ω)]
  have hc : (∑ e ∈ PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω,
      (D.erase e).card)=(PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω).card*Δ := by
    calc
      _ = ∑ _e ∈ PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω, Δ := by
        apply sum_congr rfl
        intro e he
        exact (mem_filter.mp (mem_inter.mp he).2).2
      _ = _ := by simp
  rw [hc,Nat.cast_mul]
  nlinarith only [hunit]

end MetricKMedian.FixedBatch

namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem round_count_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤
      (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ)-
        mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
  have hn := next_mass_le Δ A (roundErased A G H Z) (roundOpened A G H Z) hg hunit (roundErased_subset A G H Z)
  have he : mass g (roundErased A G H Z)=mass g (Z.biUnion (heavyActions (graphActions G) H).erase) := by
    rw [roundErased,mass,mass,card_image_of_injective _ Subtype.val_injective]
  have ho : (roundOpened A G H Z).card ≤ H.card+(Z ∩ (heavyActions (graphActions G) H).ordinary).card :=
    (card_image_le).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
  have hor : ((roundOpened A G H Z).card:ℝ) ≤ (H.card:ℝ)+((Z ∩ (heavyActions (graphActions G) H).ordinary).card:ℝ) :=
    by exact_mod_cast ho
  rw [he] at hn
  linarith only [hn,hor]

 theorem balanced_count_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    let D := heavyActions (graphActions G) H
    let Z := PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ H.card := by
  dsimp only
  have hh := round_count_change A G H (PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ) (balancedConflicts (heavyActions (graphActions G) H) Δ) ω) hg hunit
  rw [balanced_mass _ Δ ω hunit] at hh
  have hc : (((PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ)
      (balancedConflicts (heavyActions (graphActions G) H) Δ) ω) ∩
      (heavyActions (graphActions G) H).ordinary).card:ℝ) ≤
      ((PhysicalBatchLaw.balanced (balancedActions (heavyActions (graphActions G) H) Δ)
      (balancedConflicts (heavyActions (graphActions G) H) Δ) ω).card:ℝ) := by
    exact_mod_cast card_le_card (inter_subset_left (s₂ := (heavyActions (graphActions G) H).ordinary))
  linarith only [hh,hc]

 theorem unbalanced_count_change (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    let D := heavyActions (graphActions G) H
    let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤
      (H.card:ℝ)+CountStatistic.statistic
        (fun e => countOpening D Δ e-mass g (countErase D Δ e))
        (fun e f => g*(CountGeometry.overlap (countErase D Δ) e f:ℝ)) ω := by
  dsimp only
  have hn := round_count_change A G H (PhysicalBatchLaw.unbalanced (balancedActions (heavyActions (graphActions G) H) Δ) ω) hg hunit
  have hs := CountGeometry.selected_mass_bound (countErase (heavyActions (graphActions G) H) Δ)
    (countOpening (heavyActions (graphActions G) H) Δ) hg ω
  rw [masked_openings,masked_union] at hs
  dsimp only [mass] at hn hs ⊢
  linarith only [hn,hs]

end MetricKMedian.CopyState
end
end

end OAI
