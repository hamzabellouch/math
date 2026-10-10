import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaperData
import OAI.Combinatorics.KMedian.Binary.BinaryAutoFiniteLists
import OAI.Combinatorics.KMedian.Process.RoundingListOperations
import OAI.Combinatorics.KMedian.Process.TaperListProgram

namespace OAI


                                       
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset
abbrev AllRaw := (Raw × List Bool) × ℕ

def colocated (x : ℚ × Row) : ℚ := (x.2.map (fun q => if q=0 then x.1 else 0)).sum
def extras (x : (Row × List Bool) × ℕ) : List ℕ :=
  ((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))).take (x.2-(x.1.2.filter id).length)
def zeroRow (x : (Row × List Bool) × ℕ) : Row :=
  (RoundingList.indices x.1.1).map (fun i => if x.1.2[i]?.getD false || natMember (extras x,i) then 1 else 0)
def sourceRow (x : AllRaw) : Row :=
  if 1≤colocated (x.1.1.1.1,x.1.1.2) then zeroRow ((x.1.1.2,x.1.2),x.2)
  else x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))

@[fun_prop] theorem colocated_poly : Poly colocated := by
  unfold colocated
  apply comp rat_sum
  apply list_map <;> fun_prop
@[fun_prop] theorem extras_poly : Poly extras := by
  unfold extras
  have hf : Poly (fun x : (Row × List Bool) × ℕ =>
      (RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))) := by
    apply list_filter <;> fun_prop
  have hc : Poly (fun x : (Row × List Bool) × ℕ => x.1.2.filter id) := by
    apply list_filter <;> fun_prop
  exact comp (f:=fun x : List ℕ × ℕ => x.1.take x.2)
    (g:=fun x : (Row × List Bool) × ℕ => (((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))),x.2-(x.1.2.filter id).length))
    list_take (pair hf (by fun_prop))
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply list_map <;> fun_prop
@[fun_prop] theorem sourceRow_poly : Poly sourceRow := by
  unfold sourceRow
  have hm : Poly (fun x : AllRaw => x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))) := by
    apply list_map
    · unfold rationalMarginal; fun_prop
    · fun_prop
  fun_prop

 theorem colocated_list {n : ℕ} (g : ℚ) (d : Fin n → ℚ) :
    colocated (g,List.ofFn d)=rationalColocatedMass g d := by
  simp only [colocated,List.map_ofFn,List.sum_ofFn,rationalColocatedMass,Function.comp_def]
 theorem extras_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    extras ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=
      (((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val := by
  have hf : (RoundingList.indices (List.ofFn d)).filter
      (fun i => decide ((List.ofFn d)[i]?.getD 0=0) && !((List.ofFn fun k => decide (k∈own))[i]?.getD false))=
      ((zeroSources d\own).sort).map Fin.val := by
    simp only [RoundingList.indices,List.length_ofFn,RoundingList.range_finRange,List.filter_map,Function.comp_def,
      List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
    rw [show (fun i : Fin n => decide (d i=0) && !decide (i∈own))=
      (fun i : Fin n => decide (i∈zeroSources d\own)) by
      funext i; simp only [zeroSources,mem_sdiff,mem_filter,mem_univ,true_and,Bool.decide_and,decide_not]]
    rw [EncodingLists.filter_range]
    simp only [filter_univ_mem]
  simp only [extras,hf,EncodingLists.bool_card,List.map_take]
 theorem zeroRow_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    zeroRow ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (zeroMarginal d own Δ) := by
  apply List.ext_getElem
  · simp only [zeroRow,RoundingList.indices,List.length_map,List.length_range,List.length_ofFn]
  · intro k hk hk'
    have hkn : k<n := by simpa only [List.length_ofFn] using hk'
    let i : Fin n := ⟨k,hkn⟩
    simp only [zeroRow,RoundingList.indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hkn,Option.getD_some,extras_list]
    have he : natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val)=true ↔
        i∈(((zeroSources d\own).sort).take (Δ-own.card)).toFinset := by
      rw [natMember_true,List.mem_toFinset]
      simp only [List.mem_map,Fin.val_inj]
      simp only [exists_eq_right]
    change (if decide (i∈own) || natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val) then (1:ℚ) else 0)=zeroMarginal d own Δ i
    simp only [Bool.or_eq_true,decide_eq_true_eq,he,zeroMarginal,zeroSelection,extend,mem_union]
 theorem sourceRow_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    sourceRow ((((g,P),List.ofFn d),List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (sourceMarginals g P d own Δ) := by
  simp only [sourceRow,colocated_list,sourceMarginals]
  split_ifs
  · exact zeroRow_list d own Δ
  · simp only [List.map_ofFn,radius_list,Function.comp_def]
end MetricKMedian.Taper.ListOperation
end

end OAI
