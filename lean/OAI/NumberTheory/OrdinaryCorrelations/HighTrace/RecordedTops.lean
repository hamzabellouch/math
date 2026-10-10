import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeOccurrences

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def recordedTops (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) : Finset ℤ :=
  edgeVertices w E \ E.image (fun i => w.offset i.succ)

def recordU (w : ClosedLine h ℓ) (E : S.Index → Finset (Fin ℓ)) : Finset ℤ :=
  (goodOrigins w).filter (fun v => ∀ p : S.Index, S.IsCore p → v ∉ recordedTops w (E p))

lemma recordU_subset (w : ClosedLine h ℓ) (E : S.Index → Finset (Fin ℓ)) :
    recordU w E ⊆ goodOrigins w := filter_subset _ _

theorem recordU_noComponentTop (w : ClosedLine h ℓ) (E : S.Index → Finset (Fin ℓ))
    (hE : ∀ p : S.Index, E p ⊆ treeOccurrences w p) (p : S.Index) :
    NoComponentTop w (recordU w E) p (E p) := by
  intro hc i hi hv
  have hiTree := (mem_filter.mp hi).1
  have hiU := (mem_filter.mp hi).2
  have htop := (mem_filter.mp hiU).2 p hc
  have him : w.offset i.succ ∈ (E p).image (fun j => w.offset j.succ) := by
    by_contra hn
    exact htop (mem_sdiff.mpr ⟨hv,hn⟩)
  obtain ⟨j,hj,hji⟩ := mem_image.mp him
  have hjd := mem_filter.mp (hE p hj)
  have hji' : j = i := tree_destination_injective w hjd.1 hiTree hji
  simpa only [hji'] using hjd.2

lemma litEdges_subset_occurrences (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) :
    litEdges w p a ⊆ treeOccurrences w p := filter_subset _ _

lemma subtreeUnionWeight_union (w : ClosedLine h ℓ) (p : S.Index)
    (E F : Finset (Fin ℓ)) (hedge : Disjoint E F)
    (hvertex : Disjoint (edgeVertices w E) (edgeVertices w F)) :
    subtreeUnionWeight w p (E ∪ F) = subtreeUnionWeight w p E * subtreeUnionWeight w p F := by
  have hv : edgeVertices w (E ∪ F) = edgeVertices w E ∪ edgeVertices w F := by
    ext v
    simp only [edgeVertices, image_union, mem_union]
    tauto
  rw [subtreeUnionWeight, card_union_of_disjoint hedge, pow_add, hv,
    prod_union hvertex, subtreeUnionWeight, subtreeUnionWeight]
  ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
