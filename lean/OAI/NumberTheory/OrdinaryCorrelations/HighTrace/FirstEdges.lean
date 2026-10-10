import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TokenSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecPrimeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordedTopOutgoing

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

noncomputable def firstEdges (E : Finset (Fin ℓ)) : Finset (Fin ℓ) :=
  if hE : E.Nonempty then {E.min' hE} else ∅

lemma firstEdges_card (E : Finset (Fin ℓ)) : (firstEdges E).card ≤ 1 := by
  unfold firstEdges
  split_ifs <;> simp

noncomputable def taggedGoodCover (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) : Finset (Fin ℓ) :=
  univ.biUnion (fun s : TaggedSlot w hh 𝔏 a => firstEdges (tokenEdges s.2.val))

lemma taggedGoodCover_card (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :
    (taggedGoodCover w hh 𝔏 a).card ≤ Fintype.card (TaggedSlot w hh 𝔏 a) := by
  calc
    _ ≤ ∑ s : TaggedSlot w hh 𝔏 a, (firstEdges (tokenEdges s.2.val)).card := card_biUnion_le
    _ ≤ ∑ _s : TaggedSlot w hh 𝔏 a, 1 := sum_le_sum (fun s _ => firstEdges_card _)
    _ = _ := by simp

lemma good_departure_injective (w : ClosedLine h ℓ) :
    Set.InjOn (fun e : Fin ℓ => w.offset e.castSucc) (goodEdges w) := by
  intro e he f hf hef
  have hge := (mem_filter.mp he).2
  have hgf := (mem_filter.mp hf).2
  have hc : (w.treeSteps.filter (fun i => w.offset i.castSucc=w.offset e.castSucc)).card ≤ 1 := hge.2.1.le
  exact card_le_one.mp hc e (mem_filter.mpr ⟨hge.1,rfl⟩) f (mem_filter.mpr ⟨hgf.1,hef.symm⟩)

noncomputable def chargedGoodCover (w : ClosedLine h ℓ) (U : Finset ℤ) : Finset (Fin ℓ) :=
  (goodEdges w).filter (fun e => w.offset e.castSucc ∈ U)

lemma chargedGoodCover_card (w : ClosedLine h ℓ) (U : Finset ℤ) :
    (chargedGoodCover w U).card ≤ U.card :=
  card_le_card_of_injOn (fun e => w.offset e.castSucc)
    (fun _ he => (mem_filter.mp he).2)
    ((good_departure_injective w).mono (filter_subset _ _))

lemma good_origin_mem (w : ClosedLine h ℓ) (e : Fin ℓ) (he : e ∈ goodEdges w) :
    w.offset e.castSucc ∈ goodOrigins w :=
  mem_image.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩,rfl⟩

lemma pivotEdges_fibers (w : ClosedLine h ℓ) (f : S.Index → Option (TokenType w)) (e : Fin ℓ)
    (he : e ∈ goodEdges w) :
    e ∈ pivotEdges (slotShape (TypeFibers.multiplicity f)) (slotCore (TypeFibers.multiplicity f)) ↔
      ∃ p t, f p=some t ∧ t.1=true ∧ t.2.topEdge=e := by
  classical
  constructor
  · intro hp
    simp only [pivotEdges,mem_filter] at hp
    obtain ⟨⟨t,i⟩,hc,ht⟩ := hp.2
    change t.2.top.val=w.offset e.castSucc at ht
    have hn : (TypeFibers.fiber f t).Nonempty := card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    obtain ⟨p,hp⟩ := hn
    refine ⟨p,t,(TypeFibers.mem_fiber f p t).mp hp,hc,?_⟩
    symm
    apply t.2.unary_edge_eq_topEdge
    · rw [ht]
      exact (mem_filter.mp he).2.2.1
    · exact (mem_filter.mp he).1
    · exact ht.symm
  · rintro ⟨p,t,hp,hc,ht⟩
    have hj : 0 < TypeFibers.multiplicity f t := card_pos.mpr ⟨p,(TypeFibers.mem_fiber f p t).mpr hp⟩
    simp only [pivotEdges,mem_filter]
    refine ⟨he,⟨⟨t,⟨0,hj⟩⟩,hc,?_⟩⟩
    exact t.2.topEdge_origin.symm.trans (congrArg (fun i : Fin ℓ => w.offset i.castSucc) ht)

theorem good_edges_record_cover (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) :
    (goodEdges w).card ≤ Fintype.card (TaggedSlot w hh 𝔏 a) +
      (recordU w (recordAt w hh 𝔏 a).1).card +
      (pivotEdges (slotShape (TypeFibers.multiplicity (untaggedType w hh 𝔏 a)))
        (slotCore (TypeFibers.multiplicity (untaggedType w hh 𝔏 a)))).card := by
  let P := pivotEdges (slotShape (TypeFibers.multiplicity (untaggedType w hh 𝔏 a)))
    (slotCore (TypeFibers.multiplicity (untaggedType w hh 𝔏 a)))
  let T := taggedGoodCover w hh 𝔏 a
  let U := chargedGoodCover w (recordU w (recordAt w hh 𝔏 a).1)
  have hsub : goodEdges w ⊆ T ∪ U ∪ P := by
    intro e he
    by_cases hU : w.offset e.castSucc ∈ recordU w (recordAt w hh 𝔏 a).1
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨he,hU⟩))
    rcases good_origin_core_token w hh 𝔏 a _ (good_origin_mem w e he) hU with h | h
    · obtain ⟨p,hp,Q,hQ,hv⟩ := h
      have hqe : Q.topEdge=e := (Q.unary_edge_eq_topEdge (by rw [hv]; exact (mem_filter.mp he).2.2.1)
        e (mem_filter.mp he).1 hv.symm).symm
      have ht : e ∈ T := by
        apply mem_biUnion.mpr
        refine ⟨⟨p,⟨taggedShapeCode w (.inl Q),hQ⟩⟩,mem_univ _,?_⟩
        change e ∈ firstEdges Q.edges.val
        simp only [firstEdges,dite_eq_left Q.nonempty]
        exact mem_singleton.mpr hqe.symm
      exact mem_union_left _ (mem_union_left _ ht)
    · obtain ⟨p,t,hp,hc,hv⟩ := h
      have hqe : t.2.topEdge=e := (t.2.unary_edge_eq_topEdge
        (by rw [hv]; exact (mem_filter.mp he).2.2.1) e (mem_filter.mp he).1 hv.symm).symm
      exact mem_union_right _ ((pivotEdges_fibers w _ e he).mpr ⟨p,t,hp,hc,hqe⟩)
  calc
    _ ≤ (T ∪ U ∪ P).card := card_le_card hsub
    _ ≤ T.card+U.card+P.card := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add (taggedGoodCover_card w hh 𝔏 a)
      (chargedGoodCover_card w _)) _

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
