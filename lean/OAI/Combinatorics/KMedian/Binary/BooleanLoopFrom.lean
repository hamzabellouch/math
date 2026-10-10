import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanLoop

namespace OAI


                                       
section
namespace MetricKMedian.Binary.PolyProgram
open Turing Function Polynomial
variable {α σ β : Type} {ea : α → List Bool} {es : σ → List Bool} {eb : β → List Bool}
variable {init : α → σ} {body : σ → β ⊕ σ}

noncomputable def loopFrom (start : PolyProgram ea es init)
    (P : PolyProgram es (encodeLoop es eb) body) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun es body (sizes.eval (ea a).length) n (init a) (g a)) :
    PolyProgram ea eb g where
  machine := Compose.machine start.machine (Loop.machine P.machine)
  time := start.time+2*start.sizeBound+2+iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    let hs := start.outputs a
    have hstart : Trace start.machine.step hs.steps (start.machine.initialCfg (ea a))
        (start.machine.finalCfg (es (init a))) := Trace.of_iterate hs.evals_in_steps
    have hall := Compose.run start.machine (Loop.machine P.machine) hstart htrace
    refine ⟨⟨⟨_,hall.iterate_eq⟩,?_⟩⟩
    have hsize := start.length_bound a
    have hr := ht.trans (Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)
    have htime := hs.steps_le_m
    simp only [eval_add,eval_mul,eval_ofNat,eval_comp,passTime] at hr ⊢
    omega)
end MetricKMedian.Binary.PolyProgram
end

end OAI
