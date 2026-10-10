import Mathlib
import OAI.Combinatorics.KMedian.Reduction.BudgetReduction
import OAI.Combinatorics.KMedian.Reduction.ReductionOutcomesProgram
import OAI.Combinatorics.KMedian.Programs.InstanceRoundProgram
import OAI.Combinatorics.KMedian.Binary.BinaryListMapTotal

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
structure Branch where
  original : Instance
  facilities : Finset (Fin original.n)
namespace Branch
def view (B : Branch) : Raw × Row := (InstanceProgram.view B.original,setView B.facilities)
def encode (B : Branch) : List Bool := enc B.view
def allowed (B : Branch) : Prop := B.original.k ≤ B.facilities.card
instance : DecidablePred allowed := fun B => inferInstanceAs (Decidable (B.original.k≤B.facilities.card))
def restricted (B : Branch) (h : B.allowed) : Instance := B.original.restrictFacilities B.facilities h
noncomputable def allowedProgram : PolyProgram encode encodeBool (fun B => decide B.allowed) :=
  (by fun_prop : Poly (fun x : Raw × Row => decide (x.1.2.1≤card x.2))).program.recode view (fun _ => rfl) (fun B => by
    apply congrArg encodeBool
    simp only [view,InstanceProgram.view,card_view,allowed]
    rfl)
def restrictedData (x : Raw × Row) : Raw := ((x.1.1.1,x.2),x.1.2)
@[fun_prop] theorem restrictedData_poly : Poly restrictedData := by unfold restrictedData; fun_prop
 theorem restrictedData_view (B : Branch) (h : B.allowed) : restrictedData B.view=InstanceProgram.view (B.restricted h) := rfl
noncomputable def restrictedProgram : PolyProgram (fun B : {B : Branch // B.allowed} => encode B.val) InstanceProgram.encode
    (fun B => B.val.restricted B.property) :=
  restrictedData_poly.program.recode
    (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl)
    (fun B => congrArg enc (restrictedData_view B.val B.property))
end Branch
variable (r : ℕ) (hr : 0<r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def branchOut (B : Branch) : List (Finset (Fin B.original.n)) :=
  if h : B.allowed then outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b else []
noncomputable def goodProgram : PolyProgram (fun B : {B : Branch // B.allowed} => Branch.encode B.val)
    (enc : Table → List Bool) (fun B => (outcomes B.val.original B.val.facilities
      ((B.val.restricted B.property).computedPseudo r hr p c) δ c b).map setView) :=
  (((identity enc).recode (fun B : {B : Branch // B.allowed} => B.val.view) (fun _ => rfl) (fun _ => rfl)).fanout
    (Branch.restrictedProgram.comp (InstanceProgram.pseudoProgram r hr p c)) |>.comp
      (by fun_prop : Poly (fun x : (Raw × Row) × Row => outcomesData δ c b (x.1.1,(x.1.2,x.2)))).program).congr
      _ (fun B => outcomesData_view B.val.original B.val.facilities _ δ c b)
noncomputable def branchProgram : PolyProgram Branch.encode (enc : Table → List Bool)
    (fun B => (branchOut r hr p c b δ B).map setView) :=
  (dependentIfTotal Branch.allowed Branch.allowedProgram (fun _ _ => ([] : Table))
    (fun B h => (outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b).map setView)
    (constant _ enc []) (goodProgram r hr p c b δ)).congr _ (by
      intro B
      unfold branchOut
      split_ifs <;> rfl)
def branchList (I : Instance) : List Branch := (branches I I.facilities a).map (fun F => ⟨I,F⟩)
noncomputable def branchListProgram : PolyProgram InstanceProgram.encode (encodeList Branch.encode) (branchList a) :=
  (by
    have h : Poly (fun x : Raw => (branchesData a (x,x.1.2)).map (fun F => (x,F))) := by
      apply list_map <;> fun_prop
    exact h.program.recode InstanceProgram.view (fun _ => rfl) (fun I => by
      unfold branchList
      change encodeList enc ((branchesData a (view I,setView I.facilities)).map (fun F => (view I,F)))=_
      rw [branchesData_view]
      simp only [encodeList_map,List.map_map,Function.comp_def,Branch.encode,Branch.view]))
def allList (I : Instance) : List (Finset (Fin I.n)) :=
  (branches I I.facilities a).flatMap (fun F => branchOut r hr p c b δ ⟨I,F⟩)
 theorem allList_toFinset (I : Instance) :
    (allList r hr p c a b δ I).toFinset=reductionOutputs (fun J => J.computedPseudo r hr p c) I δ c a b := by
  unfold allList reductionOutputs
  rw [list_toFinset_flatMap,branches_toFinset]
  apply congrArg ((sparseBranches I I.facilities a).biUnion)
  funext F
  by_cases h : I.k≤F.card
  · simp [branchOut,Branch.allowed,Branch.restricted,h]
    exact outcomes_toFinset I F ((I.restrictFacilities F h).computedPseudo r hr p c) δ c b
  · simp [branchOut,Branch.allowed,h]
noncomputable def allListProgram : PolyProgram InstanceProgram.encode (enc : Table → List Bool)
    (fun I => (allList r hr p c a b δ I).map setView) :=
  ((branchListProgram a).comp ((branchProgram r hr p c b δ).listMapTotal) |>.comp
    (listFlatten enc ([] : Row))).congr _ (by
      intro I
      simp only [Function.comp_def,branchList,List.map_map,List.flatMap,allList,List.map_flatten])
end MetricKMedian.Reduction.Program
end

end OAI
