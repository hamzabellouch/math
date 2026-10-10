import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TokenSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UntaggedEdgeCode

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

noncomputable def taggedEdgeProduct (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (e : Fin ℓ) : ℝ :=
  ∏ p : S.Index, if e ∈ (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).biUnion tokenEdges
    then (p:ℝ) else 1

lemma taggedEdgeProduct_pos (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (e : Fin ℓ) :
    0 < taggedEdgeProduct w hh 𝔏 a e := by
  apply prod_pos
  intro p _
  split_ifs
  · exact_mod_cast S.prime_mem _ p.property |>.pos
  · norm_num

lemma unorderedEdgeProduct_fibers (w : ClosedLine h ℓ) (f : S.Index → Option (TokenType w))
    (e : Fin ℓ) :
    unorderedEdgeProduct (TypeFibers.multiplicity f) (TypeFibers.unordered f) e =
      ∏ p : S.Index, TypeFibers.factor f (fun t (p : S.Index) =>
        if e ∈ t.2.edges.val then (p:ℝ) else 1) p := by
  rw [← TypeFibers.fiber_product f]
  apply prod_congr rfl
  intro t _
  by_cases he : e ∈ t.2.edges.val <;>
    simp only [TypeFibers.unordered,he,ite_true,ite_false,prod_const_one]

lemma tagged_untagged_edge_split (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (e : Fin ℓ) (p : S.Index) :
    (if e ∈ (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).biUnion tokenEdges then (p:ℝ) else 1) *
      TypeFibers.factor (untaggedType w hh 𝔏 a)
        (fun t (p : S.Index) => if e ∈ t.2.edges.val then (p:ℝ) else 1) p =
    if e ∈ (recordTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).biUnion tokenEdges then (p:ℝ) else 1 := by
  rcases he : untaggedType w hh 𝔏 a p with _ | t
  · rw [taggedTokens_of_none w hh 𝔏 a p he]
    simp only [TypeFibers.factor,he,mul_one]
  · rw [taggedTokens_of_some w hh 𝔏 a p t he,
      (untaggedType_some w hh 𝔏 a p t he).2]
    simp only [biUnion_empty,notMem_empty,ite_false,TypeFibers.factor,he,one_mul,
      singleton_biUnion,tokenEdges]

theorem record_edge_factorization (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w)
    (hlabels : ∀ i, w.label i ∈ D.members) (e : Fin ℓ) (he : e ∈ w.treeSteps) :
    taggedEdgeProduct w hh 𝔏 a e *
      unorderedEdgeProduct (TypeFibers.multiplicity (untaggedType w hh 𝔏 a))
        (TypeFibers.unordered (untaggedType w hh 𝔏 a)) e = (w.label e : ℝ) := by
  rw [unorderedEdgeProduct_fibers,taggedEdgeProduct,← prod_mul_distrib]
  simp_rw [tagged_untagged_edge_split]
  have hr := recordTokens_recover_label w hh 𝔏 a hlabels e he
  simp only [mem_biUnion]
  exact_mod_cast hr

lemma unorderedEdgeProduct_reference {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v) (e : Fin ℓ) :
    unorderedEdgeProduct (TypeFibers.multiplicity (untaggedReference H hh 𝔏 a))
      (TypeFibers.unordered (untaggedReference H hh 𝔏 a)) e =
    unorderedEdgeProduct (TypeFibers.multiplicity (untaggedType v hh 𝔏 a))
      (TypeFibers.unordered (untaggedType v hh 𝔏 a)) e := by
  rw [unorderedEdgeProduct_fibers,unorderedEdgeProduct_fibers]
  apply prod_congr rfl
  intro p _
  rcases he : untaggedType v hh 𝔏 a p with _ | t <;>
    simp only [TypeFibers.factor,untaggedReference,he,Option.map_none,Option.map_some]
  rfl

theorem record_unordered_bins {w v : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v)
    (hlabels : ∀ i, v.label i ∈ D.members) :
    unorderedBins (TypeFibers.multiplicity (untaggedReference H hh 𝔏 a))
      (taggedEdgeProduct v hh 𝔏 a) D.H τ (TypeFibers.unordered (untaggedReference H hh 𝔏 a)) := by
  intro e he
  rw [unorderedEdgeProduct_reference,
    record_edge_factorization v hh 𝔏 a hlabels e (H.trees.symm ▸ he)]
  exact ⟨D.lower _ (hlabels e),D.upper _ (hlabels e)⟩

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
