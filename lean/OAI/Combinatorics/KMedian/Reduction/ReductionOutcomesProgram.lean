import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseReduction
import OAI.Combinatorics.KMedian.Reduction.DeletionProgram
import OAI.Combinatorics.KMedian.Reduction.LocalCompletionProgram

namespace OAI


                                                
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open Enumeration
 theorem list_toFinset_flatMap {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → List β) (xs : List α) :
    (xs.flatMap f).toFinset=xs.toFinset.biUnion (fun a => (f a).toFinset) := by
  ext b; simp only [List.mem_toFinset,List.mem_flatMap,mem_biUnion]

def completions (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) : List (Finset (Fin I.n)) :=
  (choices U b).flatMap (fun H => (choices F b).map (fun B => completionSet I F B (U\H) (rationalRadii I U) δ))
 theorem completions_toFinset (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    (completions I F U δ b).toFinset=completionBranches I F U δ b := by
  simp only [completions,list_toFinset_flatMap,list_toFinset_map,choices_toFinset,completionBranches]
  ext S
  simp only [mem_biUnion,mem_image,mem_product,Prod.exists]
  constructor
  · rintro ⟨H,hH,B,hB,he⟩; exact ⟨H,B,⟨hH,hB⟩,he⟩
  · rintro ⟨H,B,⟨hH,hB⟩,he⟩; exact ⟨H,hH,B,hB,he⟩
def completionsData (δ : ℚ) (b : ℕ) (x : Raw × (Row × Row)) : Table :=
  (choicesRaw b x.2.2).flatMap (fun H => (choicesRaw b x.2.1).map (fun B =>
    completionData (((x.1,(x.2.1,B)),(radiiData (x.1,x.2.2),δ)),diff (x.2.2,H))))
@[fun_prop] theorem completionsData_poly (δ : ℚ) (b : ℕ) : Poly (completionsData δ b) := by
  unfold completionsData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem completionsData_view (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    completionsData δ b (view I,(setView F,setView U))=(completions I F U δ b).map setView := by
  simp only [completionsData,choicesRaw_choices,List.flatMap_map,List.map_map,Function.comp_def,diff_view,radiiData_view,
    completionData_view,completions,List.map_flatMap]

def outcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) : List (Finset (Fin I.n)) :=
  T::(endpoints I T c).flatMap (fun U => U::completions I F U δ b)
 theorem outcomes_toFinset (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    (outcomes I F T δ c b).toFinset=sparseOutcomes I F T δ c b := by
  simp only [outcomes,List.toFinset_cons,list_toFinset_flatMap,endpoints_toFinset,completions_toFinset,sparseOutcomes]
def outcomesData (δ : ℚ) (c b : ℕ) (x : Raw × (Row × Row)) : Table :=
  x.2.2::(endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))
@[fun_prop] theorem outcomesData_poly (δ : ℚ) (c b : ℕ) : Poly (outcomesData δ c b) := by
  unfold outcomesData
  have h : Poly (fun x : (Raw × (Row × Row)) × Row => x.2::completionsData δ b (x.1.1,(x.1.2.1,x.2))) := by
    have hh := comp (list_cons (α := Row)) (pair (snd : Poly (fun x : (Raw × (Row × Row)) × Row =>x.2))
      (show Poly (fun x : (Raw × (Row × Row)) × Row => completionsData δ b (x.1.1,(x.1.2.1,x.2))) from by fun_prop))
    exact hh
  have hh : Poly (fun x : Raw × (Row × Row) => (endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))) := by
    apply list_flatMap <;> fun_prop
  have hhh := comp (list_cons (α := Row)) (pair (show Poly (fun x : Raw × (Row × Row) => x.2.2) from by fun_prop) hh)
  exact hhh
 theorem outcomesData_view (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    outcomesData δ c b (view I,(setView F,setView T))=(outcomes I F T δ c b).map setView := by
  simp only [outcomesData,endpointsData_view,List.flatMap_map,completionsData_view,outcomes,List.map_cons,List.map_flatMap]
end MetricKMedian.Reduction.Program
end

end OAI
