import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedRounding
import OAI.Combinatorics.KMedian.Process.RoundingRunProgram

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

def active (p : Row) : Bool := decide (0<(RoundingList.fractional p).length)
@[fun_prop] theorem active_poly : Poly active := by unfold active; fun_prop
 theorem active_list {n : ℕ} (p : Vector ℚ n) : active p.toList=decide (RationalWeightedStep.fractional p).Nonempty := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort,card_pos]
 theorem first_list {n : ℕ} (p : Vector ℚ n) (h : (RationalWeightedStep.fractional p).Nonempty) :
    first p.toList=(RationalLastFraction.pick p h).val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min _ h
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

def probability (p : Row) : ℚ := if active p then p[first p]?.getD 0 else 0
@[fun_prop] theorem probability_poly : Poly probability := by unfold probability; fun_prop
 theorem probability_list {n : ℕ} (p : Vector ℚ n) : probability p.toList=RationalLastFraction.probability p := by
  unfold probability RationalLastFraction.probability
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,List.getElem?_eq_getElem
      (show (RationalLastFraction.pick p h).val<p.toList.length by simp),
      Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

def endpoint (b : Bool) (p : Row) : Row := if active p then
  (indices p).map (fun k => if k=first p then (if b then 0 else 1) else p[k]?.getD 0)
  else p
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (endpoint b) := by
  unfold endpoint
  have he : Poly (fun p : Row => (indices p).map (fun k => if k=first p then (if b then (0:ℚ) else 1) else p[k]?.getD 0)) := by
    apply list_map <;> fun_prop
  fun_prop
 theorem endpoint_list {n : ℕ} (p : Vector ℚ n) (b : Fin 2) : endpoint (decide (b=1)) p.toList=(RationalLastFraction.endpoint p b).toList := by
  unfold endpoint RationalLastFraction.endpoint
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,indices,Vector.length_toList,range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,Vector.toList_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_inj,List.getElem?_eq_getElem (show i.val<p.toList.length by simp),Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
    fin_cases b <;> simp
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]
end MetricKMedian.RoundingList.Last

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def State.last (x : RoundingProgram.State false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,x.μ.branch RationalLastFraction.probability RationalLastFraction.probability_unit RationalLastFraction.endpoint⟩
def lastRaw (x : Row × Data Row) : Row × Data Row :=
  (x.1,(branchLawData (x.2.1,x.2.2.map RoundingList.Last.probability),
    x.2.2.flatMap (fun p => [RoundingList.Last.endpoint false p,RoundingList.Last.endpoint true p])))
@[fun_prop] theorem lastRaw_poly : Poly lastRaw := by
  unfold lastRaw
  have hp : Poly (fun x : Row × Data Row => x.2.2.map RoundingList.Last.probability) := by apply list_map <;> fun_prop
  have he : Poly (fun x : Row × Data Row => x.2.2.flatMap (fun p => [RoundingList.Last.endpoint false p,RoundingList.Last.endpoint true p])) := by
    apply list_flatMap <;> fun_prop
  exact pair (by fun_prop) (pair (comp (⟨branchLawProgram⟩ : Poly branchLawData) (pair (by fun_prop) hp)) he)
 theorem lastRaw_state (x : RoundingProgram.State false) : lastRaw x.raw=(State.last x).raw := by
  change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData _)
  apply congrArg (fun d => (List.ofFn x.β,d))
  exact vectorData_branch x.μ _ RationalLastFraction.probability_unit _ RoundingList.Last.probability
    (RoundingList.Last.endpoint false) (RoundingList.Last.endpoint true)
    RoundingList.Last.probability_list (fun p => RoundingList.Last.endpoint_list p 0)
    (fun p => RoundingList.Last.endpoint_list p 1)
noncomputable def lastProgram : PolyProgram RoundingProgram.State.encode RoundingProgram.State.encode State.last :=
  lastRaw_poly.program.recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun x => by
    rw [lastRaw_state]
    exact RoundingProgram.State.encode_raw _)

def result (x : Input false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,SparseWeightedRounding.round x.β (x.positive rfl) x.p⟩
noncomputable def program : PolyProgram Input.encode RoundingProgram.State.encode result :=
  (runProgram false |>.comp lastProgram |>.comp (compressProgram false)).congr _ (fun _ => rfl)
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
