import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllCoreLit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace Finset Classical
noncomputable section
variable {S : PrimeSystem} {h ℓ : ℕ}

lemma totalUnlitCount_eq_subtype (w : ClosedLine h ℓ) (a : S.FixedResidues w) :
    totalUnlitCount w a = ∑ p : S.FixedIndex w, (unlitOccurrences w p.val (a p)).card := by
  have he := Finset.sum_subtype (F:=inferInstance) (p:=S.IsFixed w)
    (univ.filter (S.IsFixed w)) (by simp) (fixedUnlitCount w a)
  rw [sum_filter] at he
  have hf : (∑ p : S.Index, if S.IsFixed w p then fixedUnlitCount w a p else 0) =
      totalUnlitCount w a := by
    apply sum_congr rfl
    intro p hp
    by_cases hh : S.IsFixed w p <;> simp [hh,fixedUnlitCount]
  rw [hf] at he
  exact he.trans (sum_congr rfl (fun p hp => by simp [fixedUnlitCount,p.property]))

lemma cut_tree_edges_le_unlit (w : ClosedLine h ℓ) (a : S.FixedResidues w) :
    (w.treeSteps \ uncutTreeEdges w a).card ≤ totalUnlitCount w a := by
  have hs : w.treeSteps \ uncutTreeEdges w a ⊆
      univ.biUnion (fun p : S.FixedIndex w => unlitOccurrences w p.val (a p)) := by
    intro e he
    have ht := (mem_sdiff.mp he).1
    have hn : ¬ ∀ p : S.FixedIndex w, (p.val:ℕ) ∣ w.label e →
        a p+(w.offset e.castSucc : ZMod (p.val:ℕ))=0 := by
      intro ha
      exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨ht,ha⟩)
    push Not at hn
    obtain ⟨p,hp,ha⟩ := hn
    exact mem_biUnion.mpr ⟨p,mem_univ _,mem_filter.mpr ⟨mem_univ e,hp,ha⟩⟩
  rw [totalUnlitCount_eq_subtype]
  exact (card_le_card hs).trans (card_biUnion_le ..)

lemma cut_tree_edges_lt_of_core_lit (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (hc : AllCoreLit w a) (t : ℕ) (hu : repeatedCenterUnlitCount w a<t) :
    (w.treeSteps \ uncutTreeEdges w a).card < t := by
  exact (cut_tree_edges_le_unlit w a).trans_lt ((totalUnlit_eq_center w a hc).symm ▸ hu)

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
