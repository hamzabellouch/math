import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalCopyTransition
import OAI.Combinatorics.KMedian.Process.BatchOrdinalArrays

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ActionTransition
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)

abbrev Raw := ActionList.Raw × Row

def selected (x : Raw) : List ℕ := (((ActionList.codes x.1).zip x.2).filter Prod.snd).map Prod.fst
def dead (x : Raw) : Row := (indices x.1.2).map fun i =>
  ((selected x).map fun c => (ActionArrays.erase x.1 c)[i]?.getD false).any id
def sources (x : Raw) : Row := (indices x.1.2).map fun i =>
  x.1.2[i]?.getD false || natMember (selected x,i)

@[fun_prop] theorem selected_poly : Poly selected := by
  unfold selected
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop
@[fun_prop] theorem dead_poly : Poly dead := by
  unfold dead
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem sources_poly : Poly sources := by
  unfold sources
  apply list_map <;> fun_prop

variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I) (Z : Finset (HeavyAction D H))
def view : Raw := (Ordinal.view r D H,setView (Z.map (enumeration D H).symm.toEmbedding))
 theorem selected_mem (c : ℕ) : c∈selected (view r D H Z) ↔ ∃ e∈Z, Ordinal.code r D H e=c := by
  simp only [selected,view,Ordinal.codes_eq,setView,mem_map_equiv,Equiv.symm_symm,
    Gaussian.ListOperation.zip_ofFn,List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,he⟩,hc⟩
    exact ⟨enumeration D H i,of_decide_eq_true he,hc⟩
  · rintro ⟨e,he,rfl⟩
    refine ⟨_,⟨⟨(enumeration D H).symm e,rfl⟩,?_⟩,?_⟩ <;>
      simp only [Equiv.apply_symm_apply,decide_eq_true he]

 theorem selected_light (hD : ∀ i, D.source i=i) (i : Fin n) : i.val∈selected (view r D H Z) ↔
    r i∈(Z∩(heavy D H).ordinary).image (heavy D H).source := by
  rw [selected_mem]
  constructor
  · rintro ⟨e,he,hc⟩
    have hl := (Ordinal.code_light r D H e).mp (hc ▸ i.isLt)
    cases e with
    | inl h =>
      refine mem_image.mpr ⟨.inl h,mem_inter.mpr ⟨he,?_⟩,?_⟩
      · simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inl,and_self]
      · change D.source h.val=r i
        rw [hD]
        have hh : r.symm h.val=i := Fin.ext hc
        exact (r.symm.injective (hh.trans (r.symm_apply_apply i).symm))
    | inr h => cases hl
  · rintro hi
    obtain ⟨e,he,hE⟩ := mem_image.mp hi
    rcases mem_inter.mp he with ⟨he,hord⟩
    cases e with
    | inl h =>
      refine ⟨.inl h,he,?_⟩
      change D.source h.val=r i at hE
      rw [hD] at hE
      simp only [Ordinal.code,hE,OrderIso.symm_apply_apply]
    | inr h => simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inr,Bool.false_eq_true,and_false] at hord

 theorem dead_view : dead (view r D H Z)=Ordinal.sets r (Z.biUnion (heavy D H).erase) := by
  unfold dead
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map,Function.comp_def,id_eq,List.any_eq_true,decide_eq_true_eq,mem_biUnion]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,he,rfl⟩ := (selected_mem r D H Z c).mp hc
    dsimp only [view] at hv
    rw [Ordinal.erase_code,Ordinal.sets_eq] at hv
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq] at hv
    exact ⟨e,he,hv⟩
  · rintro ⟨e,he,hi⟩
    refine ⟨Ordinal.code r D H e,(selected_mem r D H Z _).mpr ⟨e,he,rfl⟩,?_⟩
    dsimp only [view]
    rw [Ordinal.erase_code,Ordinal.sets_eq]
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true hi]

 theorem sources_view (hD : ∀ i, D.source i=i) : sources (view r D H Z)=Ordinal.sets r
    (H∪(Z∩(heavy D H).ordinary).image (heavy D H).source) := by
  unfold sources
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,Bool.or_eq_true,
    decide_eq_true_eq,natMember_true,mem_union]
  exact or_congr Iff.rfl (selected_light r D H Z hD i)

end MetricKMedian.RationalBatchData.ActionTransition
end

end OAI
