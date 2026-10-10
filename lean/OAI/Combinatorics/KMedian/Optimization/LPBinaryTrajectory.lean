import Mathlib
import OAI.Combinatorics.KMedian.Optimization.LPMinimumSelection
import OAI.Combinatorics.KMedian.Binary.BinaryIterations
import OAI.Combinatorics.KMedian.Optimization.LPBinaryStart

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

noncomputable def statePolynomial (r : ℕ) : Polynomial ℕ :=
  2*(Program.startProgram r).sizeBound+1+X*(2*(3*heightPolynomial r+10)+1)

 theorem state_size (r : ℕ) (hr : 0 < r) (I : Input) (t : ℕ) (ht : t ≤ rawSteps r I.raw) :
    (es (update^[t] (start r I))).length ≤ (statePolynomial r).eval I.encode.length := by
  rw [update_iterate]
  have hc : (ec (rawContext r I.raw)).length ≤ (Program.startProgram r).sizeBound.eval I.encode.length := by
    have hh := (Program.startProgram r).length_bound I
    change (encodePair ec er (rawContext r I.raw,rawInitial I.raw)).length ≤ (Program.startProgram r).sizeBound.eval I.encode.length at hh
    rw [encodePair_length] at hh
    dsimp only at hh
    omega
  have hy := iterate_size I r hr t (by rwa [rawSteps_eq] at ht)
  change (encodePair ec er (rawContext r I.raw,I.iterate r t)).length ≤ _
  rw [encodePair_length]
  dsimp only
  simp only [statePolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,heightPolynomial_eval]
  omega

def states (r : ℕ) (I : Input) : List State := Iteration.iterates update (start r I) (rawSteps r I.raw)
def trajectory (r : ℕ) (I : Input) : Rows := (states r I).map Prod.snd

theorem states_eq (r : ℕ) (I : Input) :
    states r I=List.ofFn (fun t : Fin (rawSteps r I.raw) => (rawContext r I.raw,I.iterate r t.val)) := by
  rw [states,Iteration.iterates_eq,range_ofFn,List.map_ofFn]
  congr 1
  funext t
  exact update_iterate r I t.val
 theorem trajectory_eq (r : ℕ) (I : Input) :
    trajectory r I=List.ofFn (fun t : Fin (rawSteps r I.raw) => I.iterate r t.val) := by
  simp only [trajectory,states_eq,List.map_ofFn]
  rfl

def value (s : State) : ℚ := Truncated.objective s.1.1 s.2 s.1.2.1
def choose (ss : List State) : State := selectMinimum value ss (([],(0,(0,0))),[])
def result (r : ℕ) (I : Input) : Row := (choose (states r I)).2

namespace Program
noncomputable def statesProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode (encodeList es) (states r) :=
  (updateProgram.iteratesFrom (startProgram r) (stepsProgram r) (([],(0,(0,0))),[])
    (stepsPolynomial r) (statePolynomial r)
    (fun I => by rw [stepsPolynomial_eval,rawSteps_eq]; exact steps_bound I r)
    (state_size r hr)).congr _ (fun _ => rfl)
noncomputable def trajectoryProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode ers (trajectory r) :=
  ((statesProgram r hr).comp ((snd ec er).listMap (([],(0,(0,0))),[]))).congr _ (fun _ => rfl)
noncomputable def valueProgram : PolyProgram es Ratio.encode value := by
  let c := fst ec er
  let ds := c.comp (fst ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let H := (c.comp (snd ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))).comp (fst Ratio.encode (encodePair Ratio.encode Ratio.encode))
  exact (((ds.fanout (snd ec er)).fanout H).comp objectiveProgram).congr _ (fun _ => rfl)
noncomputable def chooseProgram : PolyProgram (encodeList es) es choose := by
  let a0 : State := (([],(0,(0,0))),[])
  let vals := valueProgram.listMap a0
  let mn := vals.comp minimumProgram
  let val := (snd Ratio.encode es).comp valueProgram
  let pred := ((fst Ratio.encode es).fanout val).comp ratEQ
  let filt := ((mn.fanout (identity (encodeList es))).comp (pred.listFilterWith a0 0))
  exact (filt.comp (listHead es a0)).congr _ (fun ss => by
    change (ss.filter (fun a => decide (minimum (ss.map value)=value a))).head?.getD a0=choose ss
    unfold choose selectMinimum
    apply congrArg (fun xs : List State => xs.head?.getD a0)
    exact List.filter_congr (fun a _ => decide_eq_decide.mpr eq_comm))

noncomputable def optimizeProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode er (result r) :=
  (((statesProgram r hr).comp chooseProgram).comp (snd ec er)).congr _ (fun _ => rfl)
end Program

 theorem value_eq (r : ℕ) (I : Input) (t : ℕ) :
    value (rawContext r I.raw,I.iterate r t)=
      TruncatedLP.objective I.distance (ProjectedSubgradient.point (I.vector r t)) (TruncatedLP.penalty r I.k) := by
  unfold value
  change Truncated.objective I.rows (I.iterate r t) (TruncatedLP.penalty r I.k)=_
  exact Truncated.objective_ofFn _ _ _

 theorem result_eq (r : ℕ) (hr : 0 < r) (I : Input) :
    result r I=List.ofFn (ProjectedSubgradient.point (TruncatedLP.optimize I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos (TruncatedLP.penalty_pos r I.k hr))) := by
  let T := TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)
  have hT : 0 < T := TruncatedLP.steps_pos _ _ _ hr I.kpos (TruncatedLP.penalty_pos r I.k hr)
  let : NeZero T := ⟨hT.ne'⟩
  unfold result choose
  have hs := states_eq r I
  rw [rawSteps_eq] at hs
  rw [hs,selectMinimum_ofFn]
  simp only [value_eq]
  unfold TruncatedLP.optimize
  simp only [Input.iterate,Input.vector]
end MetricKMedian.LPBinary
end

end OAI
