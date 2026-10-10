import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyGraphProgram
import OAI.Combinatorics.KMedian.Process.ActionTransitionList

namespace OAI


                                       
section
namespace MetricKMedian.RationalPhysicalKernel.CopyNext
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open CopyList
open CopyGraphProgram (rank_owner)
open SparseGraph.ListOperation (Row Table setView indices)
open RationalBatchData.Ordinal (sets)
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

def pick (x : List ℕ × Row) : List ℕ := ((x.1.zip x.2).filter Prod.snd).map Prod.fst
@[fun_prop] theorem pick_poly : Poly pick := by
  unfold pick
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop

 theorem pick_mem {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (S : Finset A) (k : ℕ) :
    k∈pick (active (view A),sets (ordinal A) S) ↔ ∃a∈S,(rank a.val).val=k := by
  simp only [pick,active_view,RationalBatchData.Ordinal.sets_eq,Gaussian.ListOperation.zip_ofFn,
    List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,hi⟩,hk⟩
    exact ⟨enumeration A i,of_decide_eq_true hi,hk⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨_,⟨⟨(enumeration A).symm a,rfl⟩,?_⟩,?_⟩
    · change decide (enumeration A ((enumeration A).symm a)∈S)=true
      rw [Equiv.apply_symm_apply]
      exact decide_eq_true ha
    · simp only [Equiv.apply_symm_apply]

abbrev Raw := (ℕ × Row) × (Row × Row)
def next (x : Raw) : Row := (indices x.1.2).map fun k =>
  (x.1.2[k]?.getD false && !natMember (pick (active x.1.2,x.2.1),k)) ||
    natMember ((pick (active x.1.2,x.2.2)).map (fun j => j/x.1.1),k/x.1.1)
@[fun_prop] theorem next_poly : Poly next := by
  unfold next
  have hp : Poly (fun x : Raw => (pick (active x.1.2,x.2.2)).map (fun j => j/x.1.1)) := by
    apply list_map <;> fun_prop
  apply list_map <;> fun_prop

 theorem view_get {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (k : Fin (f*Δ)) :
    (view A)[k.val]?.getD false=decide (finProdFinEquiv.symm k∈A) := by
  simp only [view,setView,List.getElem?_ofFn,dite_eq_left k.isLt,Option.getD_some,Fin.eta,mem_map_equiv]

 theorem view_eq {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    view A=List.ofFn (fun k : Fin (f*Δ) => decide (finProdFinEquiv.symm k∈A)) := by
  simp only [view,setView,mem_map_equiv]

 theorem next_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (E O : Finset A) :
    next ((Δ,view A),(sets (ordinal A) E,sets (ordinal A) O))=
    view (CopyState.next Δ A (E.image Subtype.val) (O.image (fun a => a.val.1))) := by
  unfold next
  have hl : (view A).length=f*Δ := by simp only [view,setView,List.length_ofFn]
  simp only [indices,hl,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  change List.ofFn (fun k : Fin (f*Δ) => _)=_
  conv_rhs => rw [view_eq]
  apply congrArg List.ofFn
  funext k
  let a := finProdFinEquiv.symm k
  have ha : rank a=k := finProdFinEquiv.apply_symm_apply k
  have hdiv : k.val/Δ=a.1.val := by rw [← ha,rank_owner]
  apply Bool.eq_iff_iff.mpr
  simp only [view_get,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,Bool.eq_false_iff,decide_eq_true_eq,natMember_true,
    CopyState.next,mem_union,mem_sdiff,CopyState.mem_resets]
  simp only [ne_eq,natMember_true]
  rw [pick_mem]
  apply or_congr
  · apply and_congr Iff.rfl
    apply not_congr
    simp only [mem_image]
    constructor
    · rintro ⟨b,hb,hk⟩
      exact ⟨b,hb,finProdFinEquiv.injective ((Fin.ext hk).trans ha.symm)⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨b,hb,?_⟩
      change b.val=a at hba
      rw [hba,ha]
  · rw [List.mem_map]
    simp only [mem_image]
    constructor
    · rintro ⟨j,hj,hjk⟩
      obtain ⟨b,hb,rfl⟩ := (pick_mem A O j).mp hj
      rw [rank_owner,hdiv] at hjk
      exact ⟨b,hb,Fin.ext hjk⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨(rank b.val).val,(pick_mem A O _).mpr ⟨b,hb,rfl⟩,?_⟩
      rw [rank_owner,hdiv]
      exact congrArg Fin.val hba

abbrev TransitionRaw := (ℕ × Row) × RationalBatchData.ActionTransition.Raw
def transition (x : TransitionRaw) : Row :=
  next (x.1,(RationalBatchData.ActionTransition.dead x.2,RationalBatchData.ActionTransition.sources x.2))
@[fun_prop] theorem transition_poly : Poly transition := by unfold transition; fun_prop

 theorem transition_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (RationalBatchData.graph G) H)) :
    transition ((Δ,view A),RationalBatchData.ActionTransition.view (ordinal A) (RationalBatchData.graph G) H Z)=
      view (RationalBatchData.transition A G H Z) := by
  unfold transition
  dsimp only
  have hd := RationalBatchData.ActionTransition.dead_view (ordinal A) (RationalBatchData.graph G) H Z
  have hs := RationalBatchData.ActionTransition.sources_view (ordinal A) (RationalBatchData.graph G) H Z (fun _ => rfl)
  rw [hd,hs]
  exact next_view A _ _

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
