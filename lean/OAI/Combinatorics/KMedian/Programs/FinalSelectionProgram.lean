import Mathlib
import OAI.Combinatorics.KMedian.Reduction.ReductionCostProgram
import OAI.Combinatorics.KMedian.Programs.InstanceRoundProgram

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
def feasible (I : Instance) (S : Finset (Fin I.n)) : Bool := decide (S⊆I.facilities ∧ S.Nonempty ∧ S.card≤I.k)
def feasibleData (x : Raw × Row) : Bool := InstanceProgram.subsetRaw (x.2,x.1.1.2) && x.2.any id && decide (card x.2≤x.1.2.1)
@[fun_prop] theorem feasibleData_poly : Poly feasibleData := by unfold feasibleData; fun_prop
 theorem feasibleData_view (I : Instance) (S : Finset (Fin I.n)) : feasibleData (view I,setView S)=feasible I S := by
  simp only [feasibleData,view,InstanceProgram.subsetRaw_view,Completion.Rational.PackingProgram.any_view,card_view,feasible,Bool.decide_and,Bool.and_assoc]
def annotateData (x : Raw × Table) : List SparseSelect.TaggedProgram.Tag :=
  x.2.map (fun S => (feasibleData (x.1,S),(costData (x.1,S),S)))
@[fun_prop] theorem annotateData_poly : Poly annotateData := by unfold annotateData; apply list_map <;> fun_prop
def selectRaw (x : Raw × Table) : Table := SparseSelect.TaggedProgram.raw (annotateData x)
@[fun_prop] theorem selectRaw_poly : Poly selectRaw := by unfold selectRaw; fun_prop
 theorem selectRaw_view (I : Instance) (L : List (Finset (Fin I.n))) :
    selectRaw (view I,L.map setView)=((SparseSelect.best (feasible I) (rationalCost I) L).map setView).toList := by
  let ann := fun S : Finset (Fin I.n) => (feasible I S,(rationalCost I S,setView S))
  have ha : annotateData (view I,L.map setView)=L.map ann := by
    simp only [annotateData,List.map_map,Function.comp_def,feasibleData_view,costData_view]; rfl
  unfold selectRaw
  rw [ha,SparseSelect.TaggedProgram.raw_best]
  rw [← SparseSelect.best_map (feasible I) (rationalCost I) Prod.fst (fun a => a.2.1) ann (fun _ => rfl) (fun _ => rfl)]
  simp only [Option.map_map]; rfl
def selectList (I : Instance) (L : List (Finset (Fin I.n))) : Finset (Fin I.n) :=
  (SparseSelect.best (feasible I) (rationalCost I) L).getD {I.facilities.min' I.facilities_nonempty}
def selectData (x : Raw × Table) : Row := InstanceProgram.fallbackData (x.1,selectRaw x)
@[fun_prop] theorem selectData_poly : Poly selectData := by unfold selectData; fun_prop
 theorem selectData_view (I : Instance) (L : List (Finset (Fin I.n))) :
    selectData (view I,L.map setView)=setView (selectList I L) := by
  unfold selectData
  rw [selectRaw_view]
  simp only [InstanceProgram.fallbackData,InstanceProgram.singletonData_view,selectList]
  cases SparseSelect.best (feasible I) (rationalCost I) L <;> rfl
 theorem selectList_spec (I : Instance) (L : List (Finset (Fin I.n)))
    (T : Finset (Fin I.n)) (hT : T∈L) (hTF : T⊆I.facilities) (hTne : T.Nonempty) (hTk : T.card≤I.k) :
    selectList I L⊆I.facilities ∧ (selectList I L).Nonempty ∧ (selectList I L).card≤I.k ∧ cost I (selectList I L)≤cost I T := by
  have hTp : feasible I T=true := by simp only [feasible,decide_eq_true_eq]; exact ⟨hTF,hTne,hTk⟩
  cases hb : SparseSelect.best (feasible I) (rationalCost I) L with
  | none =>
    have hf := (SparseSelect.best_spec (feasible I) (rationalCost I) L).1.mp hb T hT
    rw [hTp] at hf
    contradiction
  | some S =>
    obtain ⟨_,hS,hmin⟩ := (SparseSelect.best_spec (feasible I) (rationalCost I) L).2 S hb
    have hs : S⊆I.facilities ∧ S.Nonempty ∧ S.card≤I.k := by simpa only [feasible,decide_eq_true_eq] using hS
    simp only [selectList,hb,Option.getD_some]
    refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    have hc : (rationalCost I S:ℝ)≤(rationalCost I T:ℝ) := by exact_mod_cast hmin T hT hTp
    simpa only [I.cast_rationalCost] using hc
end MetricKMedian.Reduction.Program
end

end OAI
