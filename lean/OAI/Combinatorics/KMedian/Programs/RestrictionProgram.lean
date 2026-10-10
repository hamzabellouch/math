import Mathlib
import OAI.Combinatorics.KMedian.Reduction.SparsifyEnumeration
import OAI.Combinatorics.KMedian.Programs.BoundedEnumerationProgram
import OAI.Combinatorics.KMedian.Programs.InstanceDataProgram

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
 theorem list_toFinset_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (xs : List α) :
    (xs.map f).toFinset=xs.toFinset.image f := by ext b; simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
 theorem choices_eq_of_mem {α : Type} [DecidableEq α] (T : Finset α) (xs : List α)
    (hx : ∀a,a∈xs ↔ a∈T) (c : ℕ) :
    ((words c xs).map List.toFinset).toFinset=deletionChoices T c := by
  ext D
  simp only [List.mem_toFinset,List.mem_map,mem_deletionChoices]
  constructor
  · rintro ⟨ys,hy,rfl⟩
    obtain ⟨hl,hm⟩ := (mem_words _ _ _).mp hy
    exact ⟨fun a ha => (hx a).mp (hm a (List.mem_toFinset.mp ha)),(List.toFinset_card_le _).trans hl⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨D.toList,(mem_words _ _ _).mpr ⟨by simpa using hcard,?_⟩,by simp⟩
    intro a ha
    exact (hx a).mpr (hsub (Finset.mem_toList.mp ha))
def choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : List (Finset (Fin n)) :=
  (words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset
 theorem mem_orderList {n : ℕ} (T : Finset (Fin n)) (i : Fin n) : i∈List.ofFn (T.orderEmbOfFin rfl) ↔ i∈T := by
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨a,rfl⟩; exact T.orderEmbOfFin_mem rfl a
  · intro hi
    have h : i ∈ Set.range (T.orderEmbOfFin rfl) := by rw [T.range_orderEmbOfFin rfl]; exact hi
    exact h
 theorem choices_toFinset {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : (choices T c).toFinset=deletionChoices T c :=
  choices_eq_of_mem T _ (mem_orderList T) c
 theorem choicesRaw_choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=(choices T c).map setView :=
  choicesRaw_view T c

def arcpairs (T : Row) : List (ℕ × ℕ) :=
  (Preparation.RationalUnitInput.Program.ranks T).flatMap (fun i =>
    (Preparation.RationalUnitInput.Program.ranks T).map (fun j => (i,j)))
@[fun_prop] theorem arcpairs_poly : Poly arcpairs := by unfold arcpairs; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 def pairs {n : ℕ} (T : Finset (Fin n)) : List (Fin n × Fin n) :=
  (List.ofFn (T.orderEmbOfFin rfl)).flatMap (fun i => (List.ofFn (T.orderEmbOfFin rfl)).map (fun j => (i,j)))
 theorem arcpairs_view {n : ℕ} (T : Finset (Fin n)) : arcpairs (setView T)=(pairs T).map (fun p => (p.1.val,p.2.val)) := by
  unfold arcpairs
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr]
  simp only [pairs,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

 theorem pairs_mem {n : ℕ} (T : Finset (Fin n)) (p : Fin n × Fin n) : p∈pairs T ↔ p∈T×ˢT := by
  simp only [pairs,List.mem_flatMap,List.mem_map,mem_product]
  constructor
  · rintro ⟨i,hi,j,hj,h⟩; cases h; exact ⟨(mem_orderList T _).mp hi,(mem_orderList T _).mp hj⟩
  · rintro ⟨hi,hj⟩; exact ⟨p.1,(mem_orderList T _).mpr hi,p.2,(mem_orderList T _).mpr hj,rfl⟩

def restrictData (x : Raw × (Row × List (ℕ × ℕ))) : Row :=
  (indices x.2.1).map (fun i => get x.2.1 i &&
    (x.2.2.map (fun p => decide ((x.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.2.2[p.1]?.getD [])[i]?.getD 0))).all id)
@[fun_prop] theorem restrictData_poly : Poly restrictData := by
  unfold restrictData
  have h : Poly (fun x : (Raw × (Row × List (ℕ × ℕ))) × ℕ =>
    (x.1.2.2.map (fun p => decide ((x.1.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.1.2.2[p.1]?.getD [])[x.2]?.getD 0))).all id) := by apply comp bool_all; apply list_map <;> fun_prop
  apply list_map <;> fun_prop

 theorem restrictData_view (I : Instance) (F : Finset (Fin I.n)) (ps : List (Fin I.n × Fin I.n)) :
    restrictData (view I,(setView F,ps.map (fun p => (p.1.val,p.2.val))))=setView (witnessedRestriction I F ps.toFinset) := by
  simp only [restrictData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Bool.and_eq_true,decide_eq_true_eq,
    witnessedRestriction,mem_filter,List.map_map,List.all_map,List.all_eq_true,id_eq,List.mem_toFinset]

def branches (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) : List (Finset (Fin I.n)) :=
  (words a (pairs F)).map (fun ps => witnessedRestriction I F ps.toFinset)
 theorem branches_toFinset (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) :
    (branches I F a).toFinset=sparseBranches I F a := by
  unfold branches sparseBranches
  rw [← choices_eq_of_mem (F×ˢF) (pairs F) (pairs_mem F) a]
  simp only [list_toFinset_map,Finset.image_image,Function.comp_def]
def branchesData (a : ℕ) (x : Raw × Row) : Table :=
  (words a (arcpairs x.2)).map (fun ps => restrictData (x.1,(x.2,ps)))
@[fun_prop] theorem branchesData_poly (a : ℕ) : Poly (branchesData a) := by unfold branchesData; apply list_map <;> fun_prop
 theorem branchesData_view (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) :
    branchesData a (view I,setView F)=(branches I F a).map setView := by
  simp only [branchesData,arcpairs_view,words_map,List.map_map,Function.comp_def,branches,restrictData_view]
end MetricKMedian.Reduction.Enumeration
end

end OAI
