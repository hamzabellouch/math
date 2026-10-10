import Mathlib
import OAI.Combinatorics.KMedian.Reduction.RationalDeletion
import OAI.Combinatorics.KMedian.Programs.NearestMaskProgram
import OAI.Combinatorics.KMedian.Programs.InstanceZeroProgram
import OAI.Combinatorics.KMedian.Reduction.ReductionCostProgram
import OAI.Combinatorics.KMedian.Programs.RestrictionProgram

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def eligibleData (x : (Raw × ℚ) × Row) : Row :=
  (indices x.2).map (fun i => get x.2 i && decide (costData (x.1.1,erase (i,x.2))-costData (x.1.1,x.2)≤x.1.2))
@[fun_prop] theorem eligibleData_poly : Poly eligibleData := by unfold eligibleData; apply list_map <;> fun_prop
 theorem eligibleData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    eligibleData ((view I,B),setView U)=setView (rationalEligible I B U) := by
  simp only [eligibleData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (get (setView U) i.val && decide (costData (view I,erase (i.val,setView U))-costData (view I,setView U)≤B))=decide _
  rw [get_view,erase_view,costData_view,costData_view]
  simp only [rationalEligible,mem_filter,Bool.decide_and]
def deleteData (x : (Raw × ℚ) × Row) : Row :=
  if x.1.1.2.1 < card x.2 then
    let E := eligibleData x
    if E.any id then erase (InstanceProgram.first E,x.2) else x.2
  else x.2
@[fun_prop] theorem deleteData_poly : Poly deleteData := by unfold deleteData; fun_prop
 theorem deleteData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    deleteData ((view I,B),setView U)=setView (rationalDeleteStep I B U) := by
  unfold deleteData rationalDeleteStep
  change (if I.k < card (setView U) then _ else _)=_
  rw [card_view]
  by_cases hk : I.k < U.card
  · simp only [ite_eq_left hk]
    rw [eligibleData_view,Completion.Rational.PackingProgram.any_view]
    by_cases he : (rationalEligible I B U).Nonempty
    · simp only [decide_eq_true he,ite_true,dite_eq_left he,InstanceProgram.first_view _ he,erase_view]
    · simp only [decide_eq_false he,Bool.false_eq_true,ite_false,dite_eq_right he]
  · simp only [ite_eq_right hk]

def historyData : ℕ → (Raw × ℚ) × Row → Row
  | 0,x => x.2
  | c+1,x => deleteData (x.1,historyData c x)
@[fun_prop] theorem historyData_poly (c : ℕ) : Poly (historyData c) := by
  induction c with
  | zero => exact snd
  | succ c ih => change Poly (fun x => deleteData (x.1,historyData c x)); fun_prop
 theorem historyData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) (c : ℕ) :
    historyData c ((view I,B),setView U)=setView (rationalHistory I B U c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [historyData,rationalHistory,ih,deleteData_view]

def values (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List ℚ :=
  (choices T c).flatMap (fun D => (List.ofFn (T.orderEmbOfFin rfl)).map (fun i =>
    rationalCost I ((T\D).erase i)-rationalCost I (T\D)))
 theorem values_toFinset (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (values I T c).toFinset=deletionValues I T c := by
  ext q
  simp only [values,List.mem_toFinset,List.mem_flatMap,List.mem_map,deletionValues,mem_biUnion,mem_image]
  constructor
  · rintro ⟨D,hD,i,hi,rfl⟩
    exact ⟨D,by rw [← choices_toFinset]; exact List.mem_toFinset.mpr hD,i,(mem_orderList T i).mp hi,rfl⟩
  · rintro ⟨D,hD,i,hi,rfl⟩
    exact ⟨D,by apply List.mem_toFinset.mp; rwa [choices_toFinset],i,(mem_orderList T i).mpr hi,rfl⟩
def valuesData (c : ℕ) (x : Raw × Row) : List ℚ :=
  (choicesRaw c x.2).flatMap (fun D => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun i =>
    costData (x.1,erase (i,diff (x.2,D)))-costData (x.1,diff (x.2,D))))
@[fun_prop] theorem valuesData_poly (c : ℕ) : Poly (valuesData c) := by unfold valuesData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem valuesData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    valuesData c (view I,setView T)=values I T c := by
  simp only [valuesData,choicesRaw_choices,List.flatMap_map,Preparation.RationalUnitInput.Program.ranks_view,List.map_ofFn,
    Function.comp_def,diff_view,erase_view,costData_view,values]

def endpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List (Finset (Fin I.n)) :=
  (0::values I T c).map (fun B => rationalHistory I B T c)
 theorem endpoints_toFinset (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (endpoints I T c).toFinset=deletionEndpoints I T c := by
  simp only [endpoints,list_toFinset_map,List.toFinset_cons,values_toFinset,deletionEndpoints]
def endpointsData (c : ℕ) (x : Raw × Row) : Table :=
  (0::valuesData c x).map (fun B => historyData c ((x.1,B),x.2))
@[fun_prop] theorem endpointsData_poly (c : ℕ) : Poly (endpointsData c) := by
  unfold endpointsData
  apply list_map
  · fun_prop
  · have h := comp (list_cons (α := ℚ)) (pair (const 0 : Poly (fun _ : Raw × Row => (0:ℚ))) (valuesData_poly c))
    exact h
 theorem endpointsData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    endpointsData c (view I,setView T)=(endpoints I T c).map setView := by
  simp only [endpointsData,valuesData_view,endpoints,List.map_map,Function.comp_def,historyData_view]
end MetricKMedian.Reduction.Program
end

end OAI
