import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalSignedTerminal
import OAI.Combinatorics.KMedian.Probability.BernoulliRunProgram
import OAI.Combinatorics.KMedian.Process.RoundingRunProgram

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

abbrev BInput := SparseBernoulli.Program.Input
abbrev BState := SparseBernoulli.Program.State
abbrev ber := SparseBernoulli.Program.er

def boolState (x : (Row × Row) × List Bool) : Row :=
  (List.range x.1.1.length).map (fun i => if x.1.1[i]?.getD 0<0 then x.1.2[i]?.getD 0
    else if x.2[i]?.getD false then 1 else 0)
@[fun_prop] theorem boolState_poly : Poly boolState := by
  unfold boolState
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=fun x : (Row × Row) × List Bool => x.1.1) list_indices (by fun_prop)

 theorem point_toList {n : ℕ} (p : Vector ℚ n) : p.toList=List.ofFn (RationalWeightedStep.point p) := by
  apply List.ext_getElem <;> intros <;> simp [RationalWeightedStep.point]

 theorem boolState_list {n : ℕ} (u : Fin n → ℚ) (p : Vector ℚ n) (q : Fin n → Bool) :
    boolState ((List.ofFn u,p.toList),List.ofFn q)=(RationalSignedTerminal.state u p q).toList := by
  rw [point_toList]
  apply List.ext_getElem
  · simp only [boolState,List.length_map,List.length_range,List.length_ofFn,Vector.length_toList]
  · intro i hi hi'
    have hi'' : i<n := by simpa only [boolState,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [boolState,List.getElem_map,List.getElem_range,List.getElem?_ofFn,dite_eq_left hi'',Option.getD_some,
      RationalSignedTerminal.state,Vector.toList_ofFn,List.getElem_ofFn,SparseBernoulli.flag]

def bernoulliInput (x : Input true) : BInput := ⟨x.n,RationalWeightedStep.point x.p,x.feasible⟩
noncomputable def bernoulliInputProgram : PolyProgram Input.encode SparseBernoulli.Program.Input.encode bernoulliInput :=
  (snd erow erow).recode Input.raw (fun _ => rfl) (fun x => by
    change erow x.p.toList=erow (List.ofFn (RationalWeightedStep.point x.p))
    rw [point_toList])

def result (x : Input true) : Data Row :=
  let μ := RationalSignedTerminal.terminal x.β x.p x.feasible
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

noncomputable def program : PolyProgram Input.encode (ed erow) result := by
  let bs := bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2)
  let bl := bs.comp (SparseIntegerLaw.DependentProgram.lawProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let rows := bs.comp (SparseIntegerLaw.DependentProgram.statesProgram
    SparseBernoulli.Program.Context.encode ber SparseBernoulli.Program.view)
  let ctx : PolyProgram Input.encode (encodePair erow erow) (@Input.raw true) :=
    (PolyProgram.identity _).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let mapped := (ctx.fanout rows).comp (boolState_poly.program.listMapWith [] [])
  exact (bl.fanout mapped).congr _ (fun x => by
    simp only [result,RationalSignedTerminal.terminal,SparseIntegerLaw.map,Vector.toList_map,List.map_map]
    dsimp only [Function.comp_def,bernoulliInput,SparseBernoulli.Program.Input.state,
      SparseBernoulli.Program.view,Input.raw]
    simp only [List.map_map,Function.comp_def,boolState_list])

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
