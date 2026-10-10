import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model
import OAI.Combinatorics.KMedianRecovery.Recovery.FrameStacks

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
noncomputable def eval_trans {S : Type} {f : S → Option S} {s t : S} {z : Option S} {m n : ℕ}
    (h1 : EvalsToInTime f s (some t) m) (h2 : EvalsToInTime f t z n) : EvalsToInTime f s z (n+m) := by
  refine ⟨⟨h2.steps+h1.steps,?_⟩,Nat.add_le_add h2.steps_le_m h1.steps_le_m⟩
  change (fun s : Option S => s.bind f)^[h2.steps+h1.steps] (some s) = z
  have e1 : (fun s : Option S => s.bind f)^[h1.steps] (some s) = some t := h1.evals_in_steps
  have e2 : (fun s : Option S => s.bind f)^[h2.steps] (some t) = z := h2.evals_in_steps
  rw [Function.iterate_add_apply,e1,e2]

namespace MapLeft
variable (p : Program)

noncomputable def parse_phase (bits a : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a bits)
      (some (cfg p (.inr 1) (fun _=>[]) ((extractPrefix bits).reverse++a) (discardPrefix bits)))
      (bits.length+1) := by
  induction bits using List.twoStepInduction generalizing a with
  | nil => exact one_step (parse_nil p a)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false p [] a)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one p a)) (by decide : 1≤2)
  | cons_cons b c bits ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false p (c::bits) a)) (by simp : 1≤(false::c::bits).length+1)
    | true =>
      have hh := step_then (parse_true p c bits a) (ih (c::a))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (a xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) a ys)
      (some (cfg p (.inl p.main) (pure p p.input (a.reverse++xs)) [] ys)) (a.length+1) := by
  induction a generalizing xs with
  | nil => exact one_step (restore_nil p xs ys)
  | cons b a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons p b a xs ys) (ih (b::xs))

noncomputable def reverse_phase (xs a ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 2) (pure p p.output xs) a ys)
      (some (cfg p (.inr 3) (fun _=>[]) (xs.reverse++a) (false::ys))) (xs.length+1) := by
  induction xs generalizing a with
  | nil => exact one_step (reverse_nil p a ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons p b xs a ys) (ih (b::a))

noncomputable def encode_phase (xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 3) (fun _=>[]) xs ys)
      (some (done p (xs.reverse.flatMap (fun b => [true,b])++ys))) (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (encode_nil p ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons p b xs ys) (ih (true::b::ys))

lemma initial (xs : List Bool) : initList (program p).machine xs=cfg p (.inr 0) (fun _=>[]) [] xs := by
  rw [initList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma final (xs : List Bool) : haltList (program p).machine xs=done p xs := by
  rw [haltList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma run_initial (xs ys : List Bool) :
    runCfg p ys (initList p.machine xs)=cfg p (.inl p.main) (pure p p.input xs) [] ys := by
  rw [initList_bool]
  rfl
lemma run_final (xs ys : List Bool) :
    runCfg p ys (haltList p.machine xs)=cfg p (.inr 2) (pure p p.output xs) [] ys := by
  rw [haltList_bool]
  rfl

noncomputable def outputs (bits out : List Bool) (n : ℕ)
    (h : TM2OutputsInTime p.machine (extractPrefix bits) (some out) n) :
    TM2OutputsInTime (program p).machine bits (some (pairBits (out,discardPrefix bits)))
      (n+2*bits.length+2*out.length+4) := by
  let xs := extractPrefix bits
  let ys := discardPrefix bits
  have hparse := parse_phase p bits []
  simp only [List.append_nil] at hparse
  have hrestore := restore_phase p xs.reverse [] ys
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  rw [pure_nil] at hrestore
  have hrun : EvalsToInTime (program p).machine.step
      (runCfg p ys (initList p.machine xs)) (some (runCfg p ys (haltList p.machine out))) n := by
    refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
    exact iterate_transfer _ _ (runCfg p ys) (run_step p ys) h.steps _ _ h.evals_in_steps
  rw [run_initial,run_final] at hrun
  have hreverse := reverse_phase p out [] ys
  simp only [List.append_nil] at hreverse
  have hencode := encode_phase p out.reverse (false::ys)
  simp only [List.reverse_reverse,List.length_reverse] at hencode
  have hh := eval_trans hparse (eval_trans hrestore (eval_trans hrun (eval_trans hreverse hencode)))
  simp only [TM2OutputsInTime,Option.map_some,initial,final,pairBits,List.append_assoc,List.cons_append,List.nil_append]
  apply time_mono hh
  have hl : xs.length≤bits.length := extractPrefix_length bits
  omega

end MapLeft

noncomputable def PolyComputes.mapLeft {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun bits => pairBits (f (extractPrefix bits),discardPrefix bits)) where
  program := MapLeft.program hf.program
  time := hf.time+2*Polynomial.X+2*(Polynomial.X+hf.time*Polynomial.C hf.program.maxPush)+4
  outputs bits := by
    have hh := MapLeft.outputs hf.program bits (f (extractPrefix bits))
      (hf.time.eval (extractPrefix bits).length) (hf.outputs (extractPrefix bits))
    have hx := extractPrefix_length bits
    have ho := hf.program.output_length (hf.outputs (extractPrefix bits))
    have ht := polynomial_monotone hf.time hx
    apply time_mono hh
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C]
    nlinarith

end MetricKMedianRecovery.BitMachine

end OAI
