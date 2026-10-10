import Mathlib
import OAI.Combinatorics.KMedian.Reduction.CompletionEnumeration
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
open Preparation.RationalNearest.MaskProgram (erase erase_view insert insert_view)
open Enumeration

def getDist (x : Raw × (ℕ × ℕ)) : ℚ := (x.1.2.2[x.2.1]?.getD [])[x.2.2]?.getD 0
@[fun_prop] theorem getDist_poly : Poly getDist := by unfold getDist; fun_prop
 theorem getDist_view (I : Instance) (i j : Fin I.n) : getDist (view I,(i.val,j.val))=I.distance i j := by
  simp only [getDist,view,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def radiiData (x : Raw × Row) : List ℚ := (indices x.2).map (fun t => nearestData (x.1.2.2[t]?.getD [],erase (t,x.2)))
@[fun_prop] theorem radiiData_poly : Poly radiiData := by unfold radiiData; apply list_map <;> fun_prop
 theorem radiiData_view (I : Instance) (U : Finset (Fin I.n)) : radiiData (view I,setView U)=List.ofFn (rationalRadii I U) := by
  simp only [radiiData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change List.ofFn (fun t : Fin I.n => nearestData (List.ofFn (I.distance t),erase (t.val,setView U)))=_
  simp only [erase_view,nearestData_view]
  rfl

abbrev LocalRaw := (Raw × (Row × Row)) × (List ℚ × ℚ)
def candidatesData (x : LocalRaw × ℕ) : Row :=
  (indices x.1.1.2.1).map (fun a => get x.1.1.2.1 a &&
    decide (getDist (x.1.1.1,(x.2,a))≤x.1.2.2*(x.1.2.1[x.2]?.getD 0)))
@[fun_prop] theorem candidatesData_poly : Poly candidatesData := by unfold candidatesData; apply list_map <;> fun_prop
 theorem candidatesData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    candidatesData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (rationalCandidates I F r δ t) := by
  simp only [candidatesData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  change (get (setView F) a.val && decide (getDist (view I,(t.val,a.val))≤δ*((List.ofFn r)[t.val]?.getD 0)))=decide _
  rw [get_view,getDist_view]
  simp only [List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,rationalCandidates,mem_filter,Bool.decide_and]

def weightData (x : LocalRaw × (ℕ × ℕ)) : ℚ :=
  ((indices x.1.1.1.1.1).map (fun j => if get x.1.1.1.1.1 j &&
    decide (3*getDist (x.1.1.1,(j,x.2.1))≤x.1.2.1[x.2.1]?.getD 0) then
      nearestData (x.1.1.1.2.2[j]?.getD [],insert (x.2.2,x.1.1.2.2)) else 0)).sum
@[fun_prop] theorem weightData_poly : Poly weightData := by unfold weightData; apply comp rat_sum; apply list_map <;> fun_prop
 theorem weightData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t a : Fin I.n) :
    weightData (((view I,(setView F,setView B)),(List.ofFn r,δ)),(t.val,a.val))=localWeight I r B t a := by
  unfold weightData
  change ((indices (setView I.clients)).map (fun j => _)).sum=_
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  change (List.ofFn (fun j : Fin I.n => if get (setView I.clients) j.val && decide (3*getDist (view I,(j.val,t.val))≤(List.ofFn r)[t.val]?.getD 0) then
    nearestData ((List.ofFn (fun i => List.ofFn (I.distance i)))[j.val]?.getD [],insert (a.val,setView B)) else 0)).sum=_
  simp only [get_view,getDist_view,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,insert_view,nearestData_view,Bool.and_eq_true,decide_eq_true_eq,List.sum_ofFn]
  rw [← Finset.sum_filter]
  change (∑j∈univ.filter (fun j => j∈I.clients ∧ 3*I.distance j t≤r t),rationalNearest I j (Insert.insert a B))=_
  have he : univ.filter (fun j => j∈I.clients ∧ 3*I.distance j t≤r t)=rationalRegion I r t := by ext j; simp [rationalRegion]
  rw [he]; rfl

def pickData (x : List ℚ × Row) : Row :=
  if x.2.any id then InstanceProgram.singletonRaw (x.2,MetricKMedian.MaskProgram.nearest x) else x.2.map (fun _ => false)
@[fun_prop] theorem pickData_poly : Poly pickData := by unfold pickData; fun_prop
 theorem pickData_view {n : ℕ} (w : Fin n → ℚ) (K : Finset (Fin n)) :
    pickData (List.ofFn w,setView K)=setView (pickSingleton K w) := by
  unfold pickData pickSingleton
  rw [Completion.Rational.PackingProgram.any_view]
  by_cases h : K.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,nearest_view w K h,InstanceProgram.singletonRaw_view]
    rfl
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]

def localData (x : LocalRaw × ℕ) : Row :=
  pickData ((indices x.1.1.2.1).map (fun a => weightData (x.1,(x.2,a))),candidatesData x)
@[fun_prop] theorem localData_poly : Poly localData := by unfold localData; apply comp pickData_poly; apply pair; apply list_map <;> fun_prop; fun_prop
 theorem localData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    localData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (localChoice I F B r δ t) := by
  unfold localData
  rw [candidatesData_view]
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change pickData (List.ofFn (fun a : Fin I.n => weightData (((view I,(setView F,setView B)),(List.ofFn r,δ)),(t.val,a.val))),
    setView (rationalCandidates I F r δ t))=setView (localChoice I F B r δ t)
  simp only [weightData_view]
  exact pickData_view _ _

def unionData (x : Row × Table) : Row := (indices x.1).map (fun i => (x.2.map (fun S => get S i)).any id)
@[fun_prop] theorem unionData_poly : Poly unionData := by unfold unionData; apply list_map; apply comp bool_any; apply list_map <;> fun_prop; fun_prop
 theorem unionData_view {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) :
    unionData (setView S,L.map setView)=setView (L.toFinset.biUnion id) := by
  simp only [unionData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_map,List.any_eq_true,id_eq,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq,
    mem_biUnion,List.mem_toFinset]

def completionData (x : LocalRaw × Row) : Row := union (x.1.1.2.2,unionData (x.2,
  (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))))
@[fun_prop] theorem completionData_poly : Poly completionData := by
  unfold completionData
  have hm : Poly (fun x : LocalRaw × Row => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))) := by apply list_map <;> fun_prop
  fun_prop
 theorem completionData_view (I : Instance) (F B G : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) :
    completionData (((view I,(setView F,setView B)),(List.ofFn r,δ)),setView G)=setView (completionSet I F B G r δ) := by
  unfold completionData
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  simp only [List.map_ofFn,Function.comp_def,localData_view]
  have he : List.ofFn (fun t => setView (localChoice I F B r δ (G.orderEmbOfFin rfl t)))=
      (List.ofFn (fun t => localChoice I F B r δ (G.orderEmbOfFin rfl t))).map setView := by simp only [List.map_ofFn,Function.comp_def]
  rw [he,unionData_view,union_view]
  apply congrArg setView
  unfold completionSet
  congr 1
  ext i
  simp only [mem_biUnion,id_eq,List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨_,⟨t,rfl⟩,hi⟩; exact ⟨_,G.orderEmbOfFin_mem rfl t,hi⟩
  · rintro ⟨t,ht,hi⟩
    obtain ⟨a,ha⟩ := (List.mem_ofFn.mp ((mem_orderList G t).mpr ht))
    subst t
    exact ⟨_,⟨a,rfl⟩,hi⟩
end MetricKMedian.Reduction.Program
end

end OAI
