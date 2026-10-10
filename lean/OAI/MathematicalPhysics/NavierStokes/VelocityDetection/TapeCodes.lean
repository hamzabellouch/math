import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.StacksLookup
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability

namespace OAI

noncomputable section
namespace VelocityDetection.TapeCodes
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def word (w : List (Fin b)) : ℕ := Nat.ofDigits b (w.map Fin.val)

omit [NeZero b] in
@[simp] theorem word_nil : word ([] : List (Fin b)) = 0 := rfl

omit [NeZero b] in
@[simp] theorem word_cons (a : Fin b) (w : List (Fin b)) :
    word (a :: w) = a.val + b * word w := rfl

theorem word_extend (w : List (Fin b)) (n : ℕ) :
    word (w ++ List.replicate n default) = word w := by
  simp [word, List.map_append, List.map_replicate]

def half (w : ListBlank (Fin b)) : ℕ :=
  w.liftOn word (fun _ _ ⟨n, hn⟩ => by rw [hn, word_extend])

@[simp] theorem half_mk (w : List (Fin b)) : half (ListBlank.mk w) = word w := rfl

@[simp] theorem half_cons (a : Fin b) (w : ListBlank (Fin b)) :
    half (w.cons a) = a.val + b * half w := by
  induction w using ListBlank.induction_on
  rfl

@[simp] theorem half_mod (w : ListBlank (Fin b)) : half w % b = w.head.val := by
  rw [← ListBlank.cons_head_tail w, half_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt w.head.isLt, ListBlank.head_cons]

@[simp] theorem half_div (w : ListBlank (Fin b)) : half w / b = half w.tail := by
  rw [← ListBlank.cons_head_tail w, half_cons,
    Nat.add_mul_div_left _ _ (NeZero.pos b), Nat.div_eq_of_lt w.head.isLt,
    zero_add, ListBlank.tail_cons]

theorem half_head_tail (w : ListBlank (Fin b)) :
    half w = w.head.val + b * half w.tail := by
  conv_lhs => rw [← ListBlank.cons_head_tail w, half_cons]

def tape (q : Fin N) (T : Tape (Fin b)) : Stacks.Configuration (Fin N) :=
  ⟨q, half T.left, half T.right₀⟩

omit [NeZero N] in
@[simp] theorem tape_read (q : Fin N) (T : Tape (Fin b)) :
    (tape q T).rightStack % b = T.head.val := by
  simp [tape, Tape.right₀, Nat.mod_eq_of_lt T.head.isLt]

def rule (a : Fin b) (q : Fin N) : TM0.Stmt (Fin b) → Rule (Fin N) b
  | .move .left => ⟨q, a, .left⟩
  | .move .right => ⟨q, a, .right⟩
  | .write β => ⟨q, β, .stay⟩

def table (M : TM0.Machine (Fin b) (Fin N)) : Fin N → Fin b → Option (Rule (Fin N) b) :=
  fun q a => (M q a).map (fun p => rule a p.1 p.2)

def config (c : TM0.Cfg (Fin b) (Fin N)) : Stacks.Configuration (Fin N) := tape c.q c.Tape

omit [NeZero N] in
theorem apply_rule (q q' : Fin N) (T : Tape (Fin b)) (s : TM0.Stmt (Fin b)) :
    Stacks.applyRule (rule T.head q' s) (tape q T) =
      tape q' (match s with | .move d => T.move d | .write a => T.write a) := by
  cases T with | mk a L R =>
    have hd : (a.val + b * half R) / b = half R := by
      rw [Nat.add_mul_div_left _ _ (NeZero.pos b), Nat.div_eq_of_lt a.isLt, zero_add]
    cases s with
    | move d =>
      cases d
      · simp only [rule, Stacks.applyRule, Stacks.update, tape, Tape.right₀, Tape.move,
          half_cons, half_mod, half_div, hd]
        congr 1
        ring
      · simp only [rule, Stacks.applyRule, Stacks.update, tape, Tape.right₀, Tape.move,
          half_cons, hd]
        congr 1
        · omega
        · exact half_head_tail R
    | write a' =>
      simp only [rule, Stacks.applyRule, Stacks.update, Stacks.replace_digit,
        tape, Tape.right₀, Tape.write, half_cons, hd]
      congr 1
      omega

def partialStep (M : TM0.Machine (Fin b) (Fin N)) (c : Stacks.Configuration (Fin N)) :
    Option (Stacks.Configuration (Fin N)) :=
  (Stacks.lookup (NeZero.pos b) (table M) c).map (fun r => Stacks.applyRule r c)

theorem lookup_config (M : TM0.Machine (Fin b) (Fin N)) (c : TM0.Cfg (Fin b) (Fin N)) :
    Stacks.lookup (NeZero.pos b) (table M) (config c) = table M c.q c.Tape.head := by
  unfold Stacks.lookup config
  have hh : (⟨(tape c.q c.Tape).rightStack % b, Nat.mod_lt _ (NeZero.pos b)⟩ : Fin b) =
      c.Tape.head := Fin.ext (tape_read c.q c.Tape)
  rw [hh]
  rfl

theorem step_config (M : TM0.Machine (Fin b) (Fin N)) (c : TM0.Cfg (Fin b) (Fin N)) :
    partialStep M (config c) = (TM0.step M c).map config := by
  rw [partialStep, lookup_config]
  cases h : M c.q c.Tape.head with
  | none => simp [table, TM0.step, h]
  | some p =>
    rcases p with ⟨q', s⟩
    simp only [table, TM0.step, h, Option.map_some]
    congr 1
    dsimp only [config]
    cases s <;> exact apply_rule c.q q' c.Tape _

theorem respects (M : TM0.Machine (Fin b) (Fin N)) :
    StateTransition.Respects (TM0.step M) (partialStep M) (fun c d => config c = d) := by
  apply StateTransition.fun_respects.mpr
  intro c
  cases h : TM0.step M c with
  | none =>
    change partialStep M (config c) = none
    rw [step_config, h, Option.map_none]
  | some d =>
    change StateTransition.Reaches₁ (partialStep M) (config c) (config d)
    exact Relation.TransGen.single (by rw [step_config, h]; rfl)

def initial (w : List (Fin b)) : Stacks.Configuration (Fin N) := ⟨0, 0, word w⟩

@[simp] theorem config_init (w : List (Fin b)) :
    config (TM0.init w : TM0.Cfg (Fin b) (Fin N)) = initial w := by
  simp [config, TM0.init, tape, Tape.mk₁, Tape.mk₂, initial]

theorem eval_dom_iff (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    (StateTransition.eval (partialStep M) (initial w)).Dom ↔ (TM0.eval M w).Dom := by
  simpa only [config_init, TM0.eval, Part.map_Dom] using
    (StateTransition.tr_eval_dom (respects M) (a₁ := TM0.init w) rfl)

theorem initial_fits (hb : 0 < b) (w : List (Fin b)) :
    (initial (N := N) w).leftStack < capacity b (w.length + 1) 0 ∧
      (initial (N := N) w).rightStack < capacity b (w.length + 1) 0 := by
  refine ⟨pow_pos (NeZero.pos b) _, ?_⟩
  have hword : word w < b ^ w.length := by
    induction w with
    | nil => simp
    | cons a w ih =>
      simpa only [word_cons, List.length_cons, pow_succ', add_comm] using
        (Stacks.packed_lt a.isLt ih)
  apply hword.trans_le
  change b ^ w.length ≤ b ^ (w.length + 1 + 0)
  exact Nat.pow_le_pow_right (by omega : 0 < b) (by omega)

end VelocityDetection.TapeCodes
end

end OAI
