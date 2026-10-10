import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Directed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreePieceWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ShapeFromGrows

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma connected_lit_component (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) (hconn : ActiveConnected w hh p a)
    (e : Fin ℓ) (he : e ∈ litEdges w p a) :
    componentEdges w hh (litEdges w p a)
      ((edgeGraph w hh (litEdges w p a)).connectedComponentMk (w.offset e.castSucc)) =
        litEdges w p a := by
  apply filter_eq_self.mpr
  intro j hj
  apply SimpleGraph.ConnectedComponent.eq.mpr
  exact hconn _ (departure_mem_vertices w j) _ (departure_mem_vertices w e)
    (mem_filter.mp hj).2 (mem_filter.mp he).2

lemma untagged_fixed_shape (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index) (a : ZMod (p : ℕ))
    (ht : ¬fixedIsTagged w hh 𝔏 p a) (hne : (treeOccurrences w p).Nonempty) :
    ∃ Q : Shape w, Q.edges.val = treeOccurrences w p := by
  have hconn : ActiveConnected w hh p a := by
    by_contra hn
    exact ht (Or.inr (Or.inl hn))
  have hl := untagged_fixed_edges w hh 𝔏 p a ht
  let E := litEdges w p a
  have hE : E.Nonempty := by simpa only [E,hl] using hne
  let e := E.min' hE
  have hem : e ∈ E := min'_mem E hE
  let c := (edgeGraph w hh E).connectedComponentMk (w.offset e.castSucc)
  have hc : c ∈ edgeComponents w hh E := mem_image.mpr ⟨e,hem,rfl⟩
  have heq : componentEdges w hh E c = E := connected_lit_component w hh p a hconn e hem
  have hsub : E ⊆ w.treeSteps := (filter_subset _ _).trans (filter_subset _ _)
  have hg := component_grows w hh hsub c hc
  exact ⟨shapeFromGrows w _ _ hg (componentEdges_nonempty w hh E c hc),heq.trans hl⟩

theorem record_untagged_shape (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : LocalToken ℓ) (ht : t ∈ recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p)
    (hu : t.1 = false) : t.2.1 = false ∧ ∃ Q : Shape w, Q.edges.val = tokenEdges t := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho] at ht
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf] at ht
      by_cases htag : (recordAt w hh 𝔏 a).2 p = true
      · rw [ite_eq_left htag] at ht
        have h := taggedPieces_tagged w hh _ _ ht
        rw [hu] at h
        contradiction
      · rw [ite_eq_right htag] at ht
        have he : t = (false,false,(recordAt w hh 𝔏 a).1 p) := mem_singleton.mp ht
        subst t
        let pf : S.FixedIndex w := ⟨p,hf⟩
        have hn : ¬fixedIsTagged w hh 𝔏 p (a pf) :=
          fun htagged => htag ((recordAt_tag w hh 𝔏 a pf ho).mpr htagged)
        refine ⟨rfl,?_⟩
        have hE := recordAt_edges w hh 𝔏 a pf
        change (recordAt w hh 𝔏 a).1 p = _ at hE
        change ∃ Q : Shape w, Q.edges.val = (recordAt w hh 𝔏 a).1 p
        rw [hE,untagged_fixed_edges w hh 𝔏 p (a pf) hn]
        exact untagged_fixed_shape w hh 𝔏 p (a pf) hn ho
    · rw [ite_eq_right hf] at ht
      obtain ⟨e,he,rfl⟩ := mem_image.mp ht
      by_cases htag : singletonIsTagged w 𝔏 p e
      · simp only [freePiece,htag,ite_true] at hu
        contradiction
      · rw [freePiece,ite_eq_right htag]
        exact ⟨rfl,⟨shapeFromGrows w _ {e} (singleton_grows w e (mem_filter.mp he).1)
          (singleton_nonempty e),rfl⟩⟩
  · rw [recordTokens,ite_eq_right ho] at ht
    exact False.elim (Finset.notMem_empty _ ht)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
