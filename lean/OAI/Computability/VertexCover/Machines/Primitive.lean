import Mathlib
import OAI.Computability.VertexCover.Machines.Pair

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine
open Turing Turing.TM2
open UniqueGames.Foundations.Complexity

namespace Stream
variable {Q : Type} [Fintype Q]
abbrev K := Fin 3
abbrev Γ (_ : K) := Bool
abbrev State (Q : Type) := Q × Option Bool
abbrev Stmt (Q : Type) := Turing.TM2.Stmt Γ Bool (State Q)
abbrev Cfg (Q : Type) := Turing.TM2.Cfg Γ Bool (State Q)

omit [Fintype Q] in
theorem cfg_ext {c d : Cfg Q} (hl : c.l = d.l) (hv : c.var = d.var) (ht : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases ht; rfl

def emit (k : K) : ℕ → (State Q → List Bool) → Stmt Q → Stmt Q
  | 0, _, p => p
  | n+1, f, p => .branch (fun s => (f s).isEmpty) p
    (.push k (fun s => (f s).headD false) (emit k n (fun s => (f s).tail) p))

omit [Fintype Q] in
theorem emit_step (k : K) (n : ℕ) (f : State Q → List Bool) (p : Stmt Q)
    (s : State Q) (t : K → List Bool) (h : (f s).length ≤ n) :
    stepAux (emit k n f p) s t =
      stepAux p s (Function.update t k ((f s).reverse ++ t k)) := by
  induction n generalizing f t with
  | zero =>
    have hf : f s = [] := List.length_eq_zero_iff.mp (by omega)
    simp [emit, hf]
  | succ n ih =>
    cases hf : f s with
    | nil => simp [emit, hf]
    | cons b bs =>
      simp only [emit, stepAux, hf, List.isEmpty_cons, Bool.cond_false, List.headD_cons]
      rw [ih (fun s => (f s).tail) (Function.update t k (b :: t k)) (by simp [hf] at h ⊢; omega)]
      simp only [hf, List.tail_cons, Function.update_self, Function.update_idem,
        List.reverse_cons, List.append_assoc, List.singleton_append]

variable (q₀ : Q) (δ : Q → Bool → Q × List Bool) (finish : Q → List Bool) (W : ℕ)

def program : Bool → Stmt Q
  | false => .pop 0 (fun s b => (s.1,b))
      (.branch (fun s => s.2.isSome)
        (emit 1 W (fun s => (δ s.1 (s.2.getD false)).2)
          (.load (fun s => ((δ s.1 (s.2.getD false)).1,s.2)) (.goto (fun _ => false))))
        (emit 1 W (fun s => finish s.1) (.goto (fun _ => true))))
  | true => .pop 1 (fun s b => (s.1,b))
      (.branch (fun s => s.2.isSome)
        (.push 2 (fun s => s.2.getD false) (.goto (fun _ => true)))
        (.load (fun _ => (q₀,none)) .halt))

abbrev machine : FinTM2 where
  K := K
  Γ := Γ
  k₀ := 0
  k₁ := 2
  Λ := Bool
  σ := State Q
  main := false
  initialState := (q₀,none)
  m := program q₀ δ finish W

def output : Q → List Bool → List Bool
  | q, [] => finish q
  | q, b :: bs => (δ q b).2 ++ output (δ q b).1 bs

def finalState : Q → List Bool → Q
  | q, [] => q
  | q, b :: bs => finalState (δ q b).1 bs

def tapes (a b c : List Bool) : K → List Bool := ![a,b,c]
@[simp] theorem tapes_zero (a b c : List Bool) : tapes a b c 0 = a := rfl
@[simp] theorem tapes_one (a b c : List Bool) : tapes a b c 1 = b := rfl
@[simp] theorem tapes_two (a b c : List Bool) : tapes a b c 2 = c := rfl

theorem update_zero (a b c d : List Bool) : Function.update (tapes a b c) 0 d = tapes d b c := by
  funext k; fin_cases k <;> simp [tapes]
theorem update_one (a b c d : List Bool) : Function.update (tapes a b c) 1 d = tapes a d c := by
  funext k; fin_cases k <;> simp [tapes]
theorem update_two (a b c d : List Bool) : Function.update (tapes a b c) 2 d = tapes a b d := by
  funext k; fin_cases k <;> simp [tapes]

abbrev cfg (phase : Bool) (q : Q) (flag : Option Bool) (a b c : List Bool) : Cfg Q :=
  ⟨some phase,(q,flag),tapes a b c⟩

variable (hδ : ∀ q b, (δ q b).2.length ≤ W) (hf : ∀ q, (finish q).length ≤ W)

include hδ in
theorem scan_cons (q : Q) (flag : Option Bool) (b : Bool) (bs t : List Bool) :
    (machine q₀ δ finish W).step (cfg false q flag (b::bs) t []) =
      some (cfg false (δ q b).1 (some b) bs ((δ q b).2.reverse ++ t) []) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, update_zero]
  rw [emit_step _ _ _ _ _ _ (hδ q b)]
  simp only [Option.getD_some, tapes_one, update_one, stepAux]

include hf in
theorem scan_nil (q : Q) (flag : Option Bool) (t : List Bool) :
    (machine q₀ δ finish W).step (cfg false q flag [] t []) =
      some (cfg true q none [] ((finish q).reverse ++ t) []) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_zero, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, update_zero]
  rw [emit_step _ _ _ _ _ _ (hf q)]
  simp only [tapes_one, update_one, stepAux]

theorem reverse_cons (q : Q) (flag : Option Bool) (b : Bool) (bs out : List Bool) :
    (machine q₀ δ finish W).step (cfg true q flag [] (b::bs) out) =
      some (cfg true q (some b) [] bs (b::out)) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_one, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, update_one, Option.getD_some, tapes_two, update_two]

theorem reverse_nil (q : Q) (flag : Option Bool) (out : List Bool) :
    (machine q₀ δ finish W).step (cfg true q flag [] [] out) =
      some (haltList (machine q₀ δ finish W) out) := by
  change step (program q₀ δ finish W) _ = _
  simp only [step, program, stepAux, tapes_one, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, update_one]
  congr 1
  apply cfg_ext <;> try rfl
  funext k; fin_cases k <;> simp [haltList, tapes, machine]

def scan_run (q : Q) (flag : Option Bool) (input t : List Bool) :
    @StateTransition.EvalsToInTime (Cfg Q) (machine q₀ δ finish W).step
      (cfg false q flag input t [])
      (some (cfg true (finalState δ q input) none []
        ((output δ finish q input).reverse ++ t) [])) (input.length+1) := by
  induction input generalizing q flag t with
  | nil => exact Pair.oneStep _ _ _ (scan_nil q₀ δ finish W hf q flag t)
  | cons b bs ih =>
    have s := Pair.oneStep _ _ _ (scan_cons q₀ δ finish W hδ q flag b bs t)
    have u := ih (δ q b).1 (some b) ((δ q b).2.reverse++t)
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s u
    simpa only [output, finalState, List.reverse_append, List.append_assoc,
      List.length_cons, Nat.add_comm 1 (bs.length+1)] using all

def reverse_run (q : Q) (flag : Option Bool) (t out : List Bool) :
    @StateTransition.EvalsToInTime (Cfg Q) (machine q₀ δ finish W).step
      (cfg true q flag [] t out)
      (some (haltList (machine q₀ δ finish W) (t.reverse++out))) (t.length+1) := by
  induction t generalizing flag out with
  | nil => exact Pair.oneStep _ _ _ (reverse_nil q₀ δ finish W q flag out)
  | cons b bs ih =>
    have s := Pair.oneStep _ _ _ (reverse_cons q₀ δ finish W q flag b bs out)
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s (ih (some b) (b::out))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm 1 (bs.length+1)] using all

theorem initial_eq (input : List Bool) :
    initList (machine q₀ δ finish W) input = cfg false q₀ none input [] [] := by
  apply cfg_ext <;> try rfl
  funext k; fin_cases k <;> simp [initList, tapes, machine]

def execution (input : List Bool) :
    TM2OutputsInTime (machine q₀ δ finish W) input (some (output δ finish q₀ input))
      (input.length + (output δ finish q₀ input).length + 2) := by
  have s := scan_run q₀ δ finish W hδ hf q₀ none input []
  have r := reverse_run q₀ δ finish W (finalState δ q₀ input) none
    (output δ finish q₀ input).reverse []
  simp only [List.append_nil] at s
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at r
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s r
  rw [← initial_eq] at all
  exact { all with steps_le_m := by have h := all.steps_le_m; omega }

omit [Fintype Q] in
include hδ hf in
theorem output_length (q : Q) (input : List Bool) :
    (output δ finish q input).length ≤ W * (input.length + 1) := by
  induction input generalizing q with
  | nil => simpa [output] using hf q
  | cons b bs ih =>
    simp only [output, List.length_append, List.length_cons]
    have h := hδ q b
    have hh := ih (δ q b).1
    calc
      _ ≤ W + W * (bs.length+1) := Nat.add_le_add h hh
      _ = _ := by ring

noncomputable def poly : Poly id id (output δ finish q₀) where
  computation := {
    tm := machine q₀ δ finish W
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C (W+1) * (Polynomial.X+1) + 1
    outputsFun := fun input => by
      simp only [id_eq, show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      have run := execution q₀ δ finish W hδ hf input
      refine { run with steps_le_m := ?_ }
      apply run.steps_le_m.trans
      have h := output_length δ finish W hδ hf q₀ input
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      nlinarith }
  finiteAlphabet := fun _ => (inferInstance : Finite Bool)

end Stream
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
