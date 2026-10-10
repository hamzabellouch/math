import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TotalUnlitCountEqSubtype
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapShapes

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace NumericalLine

theorem forest_cuts (w : NumericalLine D h ℓ) (hh : 0<h) (a : S.FixedResidues w.line)
    (hc : AllCoreLit w.line a) (hu : repeatedCenterUnlitCount w.line a<t)
    (hpack : ¬Nonempty (GapFamily w a L t)) :
    ∃ H : Finset (Fin ℓ), H ⊆ w.line.treeSteps ∧ H.card<3*t ∧
      w.line.treeSteps \ H ⊆ uncutTreeEdges w.line a ∧
      ∀ (P : TreePath w L) (p : S.FixedIndex w.line), P.IsGap a p → ∃ i,P.edge i ∈ H := by
  obtain ⟨H,hsub,hcard,hhit⟩ := w.gap_hitting hh a hpack
  refine ⟨(w.line.treeSteps \ uncutTreeEdges w.line a) ∪ H,?_,?_,?_,?_⟩
  · exact union_subset sdiff_subset (hsub.trans (filter_subset _ _))
  · have hc0 := cut_tree_edges_lt_of_core_lit w.line a hc t hu
    exact (card_union_le _ _).trans_lt (by omega)
  · intro e he
    by_contra hn
    exact (mem_sdiff.mp he).2 (mem_union_left _ (mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,hn⟩))
  · intro P p hg
    by_cases he : ∀ i,P.edge i ∈ uncutTreeEdges w.line a
    · obtain ⟨i,hi⟩ := hhit P p hg he
      exact ⟨i,mem_union_right _ hi⟩
    · push Not at he
      obtain ⟨i,hi⟩ := he
      exact ⟨i,mem_union_left _ (mem_sdiff.mpr ⟨P.tree i,hi⟩)⟩

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
