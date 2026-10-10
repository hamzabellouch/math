import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanComposition

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

 theorem polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.tm (ea a) (some (eb (f a))) (time.eval (ea a).length)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

 noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X+P.time*C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  simpa only [sizeBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    using P.machine.output_length (P.outputs a)

 noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time+2*P.sizeBound+2+Q.time.comp P.sizeBound

 noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    let hP := P.outputs a
    let hQ := Q.outputs (f a)
    have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (ea a))
        (P.machine.finalCfg (eb (f a))) := Trace.of_iterate hP.evals_in_steps
    have tQ : Trace Q.machine.step hQ.steps (Q.machine.initialCfg (eb (f a)))
        (Q.machine.finalCfg (ec (g (f a)))) := Trace.of_iterate hQ.evals_in_steps
    have h := Compose.run P.machine Q.machine tP tQ
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hl := P.length_bound a
    have hqp := (hQ.steps_le_m).trans (polynomial_eval_mono Q.time hl)
    have hpp := hP.steps_le_m
    simp only [compTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a=f' a) : PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram
end MetricKMedian.Binary
end

end OAI
