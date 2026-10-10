import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalBatchData
import OAI.Combinatorics.KMedian.Binary.BinaryAutoFiniteLists
import OAI.Combinatorics.KMedian.Process.BatchActionList
import OAI.Combinatorics.KMedian.Process.PhysicalBatchList

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.ActionArrays
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices)

def erase (x : ActionList.Raw) (c : ℕ) : Row :=
  if c<x.2.length then x.1[c]?.getD []
  else (indices x.2).map (fun i => decide (i=ActionList.child x.2.length c))
def bal (x : ActionList.Raw × ℕ) (c : ℕ) : Bool :=
  decide (c<x.1.2.length) && decide (((erase x.1 c).filter id).length=x.2)
def overlap (a b : Row) : Bool :=
  ((indices a).map (fun i => a[i]?.getD false && b[i]?.getD false)).any id
def conflict (x : ActionList.Raw × ℕ) (e f : ℕ) : Bool :=
  bal x e && bal x f && !(decide (f=e)) && overlap (erase x.1 e) (erase x.1 f)
def bias (x : ((ℚ × ℚ) × List ℚ) × ℕ) (c : ℕ) : ℚ :=
  if 1<(x.1.2[ActionList.parent x.2 c]?.getD 0) then (1+x.1.1.2)*x.1.1.1 else x.1.1.1

@[fun_prop] theorem erase_poly : Poly (fun x : ActionList.Raw × ℕ => erase x.1 x.2) := by
  unfold erase
  have hm : Poly (fun x : ActionList.Raw × ℕ => (indices x.1.2).map (fun i => decide (i=ActionList.child x.1.2.length x.2))) := by
    apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem bal_poly : Poly (fun x : (ActionList.Raw × ℕ) × ℕ => bal x.1 x.2) := by
  unfold bal
  have hm : Poly (fun x : (ActionList.Raw × ℕ) × ℕ => (erase x.1.1 x.2).filter id) := by
    apply list_filter <;> fun_prop
  fun_prop
@[fun_prop] theorem overlap_poly : Poly (fun x : Row × Row => overlap x.1 x.2) := by
  unfold overlap
  apply comp bool_any
  apply list_map <;> fun_prop
@[fun_prop] theorem conflict_poly : Poly (fun x : ((ActionList.Raw × ℕ) × ℕ) × ℕ => conflict x.1.1 x.1.2 x.2) := by
  unfold conflict; fun_prop
@[fun_prop] theorem bias_poly : Poly (fun x : (((ℚ × ℚ) × List ℚ) × ℕ) × ℕ => bias x.1 x.2) := by
  unfold bias; fun_prop

 theorem code_light {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (e : HeavyAction D H) :
    ActionCodes.code D H e<n ↔ e.isLeft=true := by
  cases e with
  | inl e => simp only [ActionCodes.code,Fin.isLt,Sum.isLeft_inl]
  | inr e => simp only [ActionCodes.code,Sum.isLeft_inr,Bool.false_eq_true,iff_false]; omega
 theorem erase_code {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (e : HeavyAction D H) :
    erase (ActionList.view D H) (ActionCodes.code D H e)=setView ((heavy D H).erase e) := by
  cases e with
  | inl e =>
    change erase (ActionList.view D H) e.val.val=setView (D.erase e.val)
    simp only [erase,ActionList.view,setView,List.length_ofFn,ite_eq_left e.val.isLt,
      List.getElem?_ofFn,dite_eq_left e.val.isLt,Option.getD_some,Fin.eta]
  | inr e =>
    have hc : ¬ n+e.val.1.val*n+e.val.2.val<n := by omega
    change erase (ActionList.view D H) (n+e.val.1.val*n+e.val.2.val)=setView {e.val.2}
    simp only [erase,ActionList.view,setView,List.length_ofFn,ite_eq_right hc,indices,
      RoundingList.range_finRange,List.map_map,Function.comp_def]
    rw [← List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext i
    rw [show ActionList.child n (n+e.val.1.val*n+e.val.2.val)=e.val.2.val from ActionList.child_code D H e]
    simp only [mem_singleton,Fin.ext_iff]
 theorem bal_code {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (Δ : ℕ) (e : HeavyAction D H) :
    bal (ActionList.view D H,Δ) (ActionCodes.code D H e)=true ↔ e∈balanced (heavy D H) Δ := by
  unfold bal
  rw [Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  rw [show (ActionList.view D H).2.length=n by simp only [ActionList.view,setView,List.length_ofFn],
    erase_code]
  have hc : ((setView ((heavy D H).erase e)).filter id).length=((heavy D H).erase e).card :=
    EncodingLists.bool_card ((heavy D H).erase e)
  rw [hc,code_light]
  change (e.isLeft=true ∧ ((heavy D H).erase e).card=Δ) ↔
    e∈((Finset.univ.filter (fun e : HeavyAction D H => e.isLeft=true)).filter
      (fun e => ((heavy D H).erase e).card=Δ))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

 theorem overlap_view {n : ℕ} (A B : Finset (Fin n)) :
    overlap (setView A) (setView B)=true ↔ (A∩B).Nonempty := by
  simp only [overlap,indices,setView,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.any_map,List.any_eq_true,List.mem_finRange,true_and,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,id_eq,Bool.and_eq_true,
    decide_eq_true_eq,Finset.Nonempty,mem_inter]

 theorem conflict_code {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (Δ : ℕ) (e f : HeavyAction D H) :
    conflict (ActionList.view D H,Δ) (ActionCodes.code D H e) (ActionCodes.code D H f)=true ↔
      f∈conflicts (heavy D H) Δ e := by
  simp only [conflict,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,bal_code,erase_code,overlap_view]
  have he : ActionCodes.code D H f≠ActionCodes.code D H e ↔ f≠e :=
    not_congr (@StrictMono.injective _ _ (ActionCodes.actionOrder D H) _ _ (ActionCodes.code_strictMono D H)).eq_iff
  simp only [he]
  unfold conflicts
  split_ifs with hb <;> simp only [mem_filter,notMem_empty,iff_false]
  · tauto
  · tauto
 theorem bias_code {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (m : Fin n → ℚ)
    (p φ : ℚ) (e : HeavyAction D H) :
    bias (((p,φ),List.ofFn m),n) (ActionCodes.code D H e)=
      RationalBatchData.bias m p φ (heavyParent D H e) := by
  simp only [bias,ActionList.parent_code,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    RationalBatchData.bias]

abbrev Raw := (((ℚ × ℚ) × List ℚ) × ℕ) × ActionList.Raw

def data (x : Raw) : SparsePhysicalBatch.ListOperation.Raw :=
  (((ActionList.codes x.2).map (bal (x.2,x.1.2)),
    (ActionList.codes x.2).map (fun e => (ActionList.codes x.2).map (conflict (x.2,x.1.2) e))),
    (x.1.1.1.1,(ActionList.codes x.2).map (bias (x.1.1,x.2.2.length))))
@[fun_prop] theorem data_poly : Poly data := by
  unfold data
  apply pair
  · apply pair
    · apply list_map <;> fun_prop
    · apply list_map
      · apply list_map
        · exact comp (g:=fun x : (Raw × ℕ) × ℕ => (((x.1.1.2,x.1.1.1.2),x.1.2),x.2)) conflict_poly (by fun_prop)
        · fun_prop
      · fun_prop
  · apply pair
    · fun_prop
    · apply list_map <;> fun_prop

theorem data_view {n : ℕ} (D : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (m : Fin n → ℚ)
    (p φ : ℚ) (Δ : ℕ) :
    data ((((p,φ),List.ofFn m),Δ),ActionList.view D H)=
    ((setView ((balanced (heavy D H) Δ).map (enumeration D H).symm.toEmbedding),
      List.ofFn (fun i => setView ((conflicts (heavy D H) Δ (enumeration D H i)).map (enumeration D H).symm.toEmbedding))),
      (p,List.ofFn (fun i => RationalBatchData.bias m p φ (heavyParent D H (enumeration D H i))))) := by
  unfold data
  dsimp only
  rw [ActionList.codes_eq]
  apply Prod.ext
  · apply Prod.ext
    · dsimp only
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact bal_code D H Δ (enumeration D H i)
    · dsimp only
      simp only [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact conflict_code D H Δ (enumeration D H i) (enumeration D H j)
  · apply Prod.ext
    · rfl
    · dsimp only
      rw [List.map_ofFn]
      have hn : (ActionList.view D H).2.length=n := by simp only [ActionList.view,setView,List.length_ofFn]
      rw [hn]
      apply congrArg List.ofFn
      funext i
      exact bias_code D H m p φ (enumeration D H i)

end MetricKMedian.RationalBatchData.ActionArrays

end

end OAI
