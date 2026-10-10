import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActiveReachable
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ConnectedSetPath
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeGraphMono
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkSupportConnected

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
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma litEdges_subset_tree (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p:ℕ)) :
    litEdges w p a ⊆ w.treeSteps := by
  intro e he
  exact (mem_filter.mp (mem_filter.mp he).1).1

lemma lit_walk_active (w : ClosedLine h ℓ) (hh : 0<h) (p : S.Index) (hph : ¬(p:ℕ) ∣ h)
    (a : ZMod (p:ℕ)) {u v : ℤ} (q : (edgeGraph w hh (litEdges w p a)).Walk u v)
    (hu : a+(u:ZMod (p:ℕ))=0) : ∀ z  ∈  q.support,a+(z:ZMod (p:ℕ))=0 := by
  induction q with
  | nil => simpa using hu
  | @cons u v z hq q ih =>
    have hv := ((active_graph_exact w hh p hph a u v).mp hq).2.2
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hu
    · exact ih hv x hx

def blockActiveSet (w : ClosedLine h ℓ) (hh : 0<h) (a : S.FixedResidues w)
    {H : Finset (Fin ℓ)} (b : Block (edgeGraph w hh (w.treeSteps\H))) (p : S.FixedIndex w) : Finset ℤ :=
  (treeVertices w).filter (fun v => v  ∈  b.walk.support ∧ a p+(v:ZMod (p.val:ℕ))=0)

theorem blockActiveSet_connected (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ))
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i  ∈  H)
    (b : Block (edgeGraph w.line hh (w.line.treeSteps\H))) (hb : b.walk.length  ≤  L)
    (p : S.FixedIndex w.line) (hph : ¬(p.val:ℕ) ∣ h) :
    ConnectedSet (edgeGraph w.line hh w.line.treeSteps) (blockActiveSet w.line hh a b p) := by
  intro u hu v hv
  obtain ⟨huT,hub,hua⟩ := mem_filter.mp hu
  obtain ⟨hvT,hvb,hva⟩ := mem_filter.mp hv
  obtain ⟨q⟩ := block_active_connected w hh a H hcut b hb p hph huT hub hvb hua hva
  let incl := edgeGraph_mono w.line hh (litEdges_subset_tree w.line p.val (a p))
  let r := q.mapLe incl
  have hr : ∀ z  ∈  r.toPath.val.support,z  ∈  q.support := by
    intro z hz
    have := r.support_toPath_subset_support hz
    simpa only [r,Walk.support_mapLe_eq_support] using this
  let cutincl := edgeGraph_mono w.line hh (sdiff_subset : w.line.treeSteps\H ⊆ w.line.treeSteps)
  let bfull := b.walk.mapLe cutincl
  have hbconn : ConnectedSet (edgeGraph w.line hh w.line.treeSteps) b.walk.support.toFinset := by
    have he := walk_support_connected bfull
    simpa only [bfull,Walk.support_mapLe_eq_support] using he
  have hbs := connectedSet_path (edgeGraph_acyclic w.line hh w.line.treeSteps (Subset.refl _))
    hbconn (List.mem_toFinset.mpr hub) (List.mem_toFinset.mpr hvb) r.toPath.val r.toPath.property
  refine ⟨r.toPath.val,?_⟩
  intro z hz
  exact mem_filter.mpr ⟨walk_vertices w.line hh q huT z (hr z hz),
    List.mem_toFinset.mp (hbs z hz),lit_walk_active w.line hh p.val hph (a p) q hua z (hr z hz)⟩

lemma block_gate_length (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) {H : Finset (Fin ℓ)}
    (b : Block (edgeGraph w.line hh (w.line.treeSteps\H))) {p : S.FixedIndex w.line}
    {root : ℤ} (hr : root  ∈  b.walk.support)
    (g : Gate (edgeGraph w.line hh w.line.treeSteps) root (blockActiveSet w.line hh a b p)) :
    g.path.length  ≤  b.walk.length := by
  have hg := (mem_filter.mp g.mem).2.1
  obtain ⟨q,hq⟩ := walk_between_support b.walk hr hg
  let incl := edgeGraph_mono w.line hh (sdiff_subset : w.line.treeSteps\H ⊆ w.line.treeSteps)
  let r := q.mapLe incl
  have he := paths_eq (edgeGraph_acyclic w.line hh _ (Subset.refl _)) g.simple r.toPath.property
  rw [he]
  exact r.length_bypass_le_length.trans (by simpa only [r,Walk.length_mapLe] using hq)

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
