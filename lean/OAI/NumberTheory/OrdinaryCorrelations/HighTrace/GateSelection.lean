import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TwoBlockRerooting
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BlockActiveCapacity
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedWitness
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BlockGateExists

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
namespace DisconnectedBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} {a : S.FixedResidues w.line}
    {H : Finset (Fin ℓ)} (F : DisconnectedBlockPair w hh a H L)

structure GateSelection where
  selected : Finset F.selected
  root₁ : ℤ
  root₂ : ℤ
  root₁_mem : root₁ ∈ treeVertices w.line
  root₂_mem : root₂ ∈ treeVertices w.line
  root₁_in : root₁ ∈ F.first.walk.support
  root₂_in : root₂ ∈ F.second.walk.support
  first : ∀ p : selected,Gate (edgeGraph w.line hh w.line.treeSteps) root₁
    (blockActiveSet w.line hh a F.first p.val.val)
  second : ∀ p : selected,Gate (edgeGraph w.line hh w.line.treeSteps) root₂
    (blockActiveSet w.line hh a F.second p.val.val)
  key : selected→ℕ
  earlier : ∀ p q : selected,gateAncestor first p q ∨ gateAncestor second p q → key p<key q

theorem gateSelection_exists
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (hph : ∀ p : F.selected,¬(p.val.val:ℕ) ∣ h)
    (hne : F.selected.Nonempty) (n : ℕ) (hn : n^8 ≤ F.selected.card) :
    ∃ g : F.GateSelection,n ≤ (2*⌈C₀*Real.log B⌉₊+1)*g.selected.card := by
  let p₀ : F.selected := ⟨hne.choose,hne.choose_spec⟩
  let root₁ := (F.witness p₀.val p₀.property).left
  let root₂ := (F.witness p₀.val p₀.property).right
  have hr₁ : root₁ ∈ F.first.walk.support := F.left_in p₀.val p₀.property
  have hr₂ : root₂ ∈ F.second.walk.support := F.right_in p₀.val p₀.property
  let g₁ : ∀ p : F.selected,Gate (edgeGraph w.line hh w.line.treeSteps) root₁
      (blockActiveSet w.line hh a F.first p.val) := fun p =>
    Classical.choice (block_gate_exists w hh a F.first p.val hr₁ (F.first_nonempty p))
  let g₂ : ∀ p : F.selected,Gate (edgeGraph w.line hh w.line.treeSteps) root₂
      (blockActiveSet w.line hh a F.second p.val) := fun p =>
    Classical.choice (block_gate_exists w hh a F.second p.val hr₂ (F.second_nonempty p))
  let emb : F.selected↪S.FixedIndex w.line := ⟨Subtype.val,Subtype.val_injective⟩
  have hG := edgeGraph_acyclic w.line hh w.line.treeSteps (Subset.refl _)
  obtain ⟨t,root,g,key,hcard,hroot,horder⟩ := two_block_rerooting hG hG g₁ g₂
    (fun p => blockActiveSet_connected w hh a H hcut F.second F.second_small p.val (hph p))
    ⌈C₀*Real.log B⌉₊ n (by simpa using hn)
    (block_active_capacity w hh a F.second emb hph)
  have hrootT : root ∈ treeVertices w.line := by
    rcases hroot with rfl|⟨p,rfl⟩
    · exact (F.witness p₀.val p₀.property).right_mem
    · exact (mem_filter.mp (g₂ p).mem).1
  have hrootB : root ∈ F.second.walk.support := by
    rcases hroot with rfl|⟨p,rfl⟩
    · exact hr₂
    · exact (mem_filter.mp (g₂ p).mem).2.1
  exact ⟨⟨t,root₁,root,(F.witness p₀.val p₀.property).left_mem,hrootT,hr₁,hrootB,
    (fun p => g₁ p.val),g,key,horder⟩,hcard⟩

end DisconnectedBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
