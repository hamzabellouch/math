import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapPathCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GateAncestor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LitEdgesSubsetTree
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExistsTreePathWithSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Expression

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal OrdinaryCorrelations.Rerooting
open OrdinaryCorrelations.ArithmeticSaving
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma block_gate_exists (w : NumericalLine D h ℓ) (hh : 0<h) (a : S.FixedResidues w.line)
    {H : Finset (Fin ℓ)} (b : Block (edgeGraph w.line hh (w.line.treeSteps\H)))
    (p : S.FixedIndex w.line) {root : ℤ} (hr : root ∈ b.walk.support)
    (hne : (blockActiveSet w.line hh a b p).Nonempty) :
    Nonempty (Gate (edgeGraph w.line hh w.line.treeSteps) root (blockActiveSet w.line hh a b p)) := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨q,hq⟩ := walk_between_support b.walk hr (mem_filter.mp hz).2.1
  exact gate_exists (q.mapLe (edgeGraph_mono w.line hh sdiff_subset)) hz

lemma block_gate_code {α : Type*} (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ))
    (huncut : w.line.treeSteps\H ⊆ uncutTreeEdges w.line a)
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (b : Block (edgeGraph w.line hh (w.line.treeSteps\H))) (hb : b.walk.length ≤ L)
    (p : α→S.FixedIndex w.line) (hph : ∀ i,¬(p i).val.val ∣ h)
    {root : ℤ} (hr : root ∈ b.walk.support) (hrT : root ∈ treeVertices w.line)
    (g : ∀ i,Gate (edgeGraph w.line hh w.line.treeSteps) root (blockActiveSet w.line hh a b (p i)))
    (i : α) : ∃ r : GapPathCode ℓ L,
      (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).eval (fun q => ((q:ℕ):ℤ))=
        (g i).vertex-root ∧
      ∀ j,(p j).val ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).support →
        gateAncestor g j i := by
  have hG := edgeGraph_acyclic w.line hh w.line.treeSteps (Subset.refl _)
  by_cases he : root=(g i).vertex
  · refine ⟨fun _ => none,?_,?_⟩
    · simp [PatternExpression.gap,SquarefreeExpression.eval,he]
    · intro j hj
      simp [PatternExpression.gap,SquarefreeExpression.support] at hj
  obtain ⟨q,hq⟩ := walk_between_support b.walk hr (mem_filter.mp (g i).mem).2.1
  obtain ⟨P,hP0,hPL,hPE,hPV⟩ := exists_treePath_with_support w hh sdiff_subset q (hq.trans hb) hrT he
  let incl := edgeGraph_mono w.line hh (sdiff_subset : w.line.treeSteps\H ⊆ w.line.treeSteps)
  have hqp : (q.bypass.mapLe incl).IsPath := by
    simpa only [Walk.isPath_def,Walk.support_mapLe_eq_support] using q.bypass_isPath
  have heq : q.bypass.mapLe incl=(g i).path := paths_eq hG hqp (g i).simple
  have hPg (v : Fin (P.length+1)) : P.vertex v ∈ (g i).path.support := by
    rw [←heq,Walk.support_mapLe_eq_support]
    exact hPV v
  have hbconn : ConnectedSet (edgeGraph w.line hh w.line.treeSteps) b.walk.support.toFinset := by
    simpa only [Walk.support_mapLe_eq_support] using walk_support_connected (b.walk.mapLe incl)
  have hgsub := connectedSet_path hG hbconn (List.mem_toFinset.mpr hr)
    (List.mem_toFinset.mpr (mem_filter.mp (g i).mem).2.1) (g i).path (g i).simple
  refine ⟨P.code,P.expression_eval.trans (by rw [hP0,hPL]),?_⟩
  intro j hj
  obtain ⟨k,hk⟩ := P.expression_support hj
  have hc : ConnectedSet (edgeGraph w.line hh w.line.treeSteps) (blockActiveSet w.line hh a b (p j)) :=
    blockActiveSet_connected w hh a H hcut b hb (p j) (hph j)
  have hza : a (p j)+(P.vertex k.castSucc:ZMod ((p j).val:ℕ))=0 :=
    P.departure_lit a (fun k => huncut (hPE k)) (p j) k hk
  have hzT : P.vertex k.castSucc ∈ treeVertices w.line := by
    obtain ⟨v,hv⟩ := P.vertex_mem k.castSucc
    exact mem_image.mpr ⟨v,mem_univ _,hv.symm⟩
  apply gate_dependency hG hc (g i) (g j)
    (mem_filter.mpr ⟨hzT,List.mem_toFinset.mp (hgsub _ (hPg k.castSucc)),hza⟩) (hPg k.castSucc)
  intro hez
  have hkz := P.distinct (hez.trans hPL.symm)
  have hh := congrArg Fin.val hkz
  simp only [Fin.val_castSucc,Fin.val_last] at hh
  exact k.isLt.ne hh

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
