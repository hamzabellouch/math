import Mathlib
import OAI.Computability.QuantumFactoring.BooleanProgram

namespace OAI

section


namespace ExactQuantumFactoring

/-- A bounded-fan-in Boolean node, with no hidden arithmetic operation. -/
inductive BoolNode (n : ℕ) where
  | constant (b : Bool)
  | copy (i : Fin n)
  | neg (i : Fin n)
  | conj (i j : Fin n)

namespace BoolNode

def eval {n : ℕ} : BoolNode n → (Fin n → Bool) → Bool
  | .constant b, _ => b
  | .copy i, x => x i
  | .neg i, x => !x i
  | .conj i j, x => x i && x j

def map {n m : ℕ} (f : Fin n → Fin m) : BoolNode n → BoolNode m
  | .constant b => .constant b
  | .copy i => .copy (f i)
  | .neg i => .neg (f i)
  | .conj i j => .conj (f i) (f j)

lemma eval_map {n m : ℕ} (f : Fin n → Fin m) (o : BoolNode n) (x : Fin m → Bool) :
    (o.map f).eval x = o.eval (x ∘ f) := by cases o <;> rfl

/-- The new wire is distinct from every preexisting wire. -/
def compileOp {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) :
    BooleanOp q ⟨n, by omega⟩ :=
  match o with
  | .constant b => .constant b
  | .copy i => .copy (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .neg i => .neg (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .conj i j => .conj (i.castLE (by omega)) (j.castLE (by omega))
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)

lemma compileOp_value {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) (x : Basis q) :
    (o.compileOp h).value x = o.eval (fun i => x (i.castLE (by omega))) := by
  cases o <;> rfl

end BoolNode

/-- Straight-line Boolean computation retaining its whole trace. Width increases
by exactly one per node, so there is no truth-table synthesis overhead. -/
inductive BoolNet (n : ℕ) : ℕ → Type
  | input : BoolNet n n
  | add {k : ℕ} (p : BoolNet n k) (o : BoolNode k) : BoolNet n (k+1)

namespace BoolNet

def count {n k : ℕ} : BoolNet n k → ℕ
  | .input => 0
  | .add p _ => p.count + 1

lemma width_eq {n k : ℕ} (p : BoolNet n k) : k = n + p.count := by
  induction p with
  | input => simp [count]
  | add p o ih => simp only [count]; omega

lemma input_le {n k : ℕ} (p : BoolNet n k) : n ≤ k := by rw [p.width_eq]; omega

def eval {n k : ℕ} : BoolNet n k → (Fin n → Bool) → (Fin k → Bool)
  | .input, x => x
  | .add p o, x => Fin.snoc (p.eval x) (o.eval (p.eval x))

@[simp] lemma eval_add_castSucc {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) (i : Fin k) : (p.add o).eval x i.castSucc = p.eval x i := by
  simp [eval]

@[simp] lemma eval_add_last {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) : (p.add o).eval x (Fin.last k) = o.eval (p.eval x) := by
  simp [eval]

lemma eval_input {n k : ℕ} (p : BoolNet n k) (x : Fin n → Bool) (i : Fin n) :
    p.eval x (i.castLE p.input_le) = x i := by
  induction p with
  | input => rfl
  | add p o ih =>
    have he : i.castLE (p.add o).input_le = (i.castLE p.input_le).castSucc := rfl
    rw [he, eval_add_castSucc, ih]

def program {n k : ℕ} (p : BoolNet n k) {q : ℕ} (h : k ≤ q) : BooleanProgram q :=
  match p with
  | .input => []
  | .add p o => p.program (by omega) ++ [⟨⟨_, by omega⟩, o.compileOp h⟩]

lemma program_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (p.program h).length = p.count := by
  induction p with
  | input => rfl
  | add p o ih => simp [program, count, ih]

lemma compile_length {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) :
    (BooleanProgram.compile (p.program h)).length ≤ 2 * p.count := by
  simpa only [program_length] using BooleanProgram.compile_length (p.program h)

/-- Append a network whose inputs are arbitrary already-computed wires.
Repeated input sources are permitted and do not cause duplicated computation. -/
def attach {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (j : ℕ) × BoolNet n j × (Fin l → Fin j) :=
  match b with
  | .input => ⟨k, a, ρ⟩
  | .add b o =>
    let c := a.attach ρ b
    ⟨c.1 + 1, c.2.1.add (o.map c.2.2), Fin.snoc (fun i => (c.2.2 i).castSucc) (Fin.last c.1)⟩

lemma attach_count {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).2.1.count = a.count + b.count := by
  induction b with
  | input => simp [attach, count]
  | add b o ih => simp only [attach, count, ih, Nat.add_assoc]

lemma attach_eval {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) :
    (a.attach ρ b).2.1.eval x ∘ (a.attach ρ b).2.2 = b.eval (a.eval x ∘ ρ) := by
  induction b with
  | input => rfl
  | @add l b o ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [attach, Function.comp_apply, Fin.snoc_last, eval_add_last, BoolNode.eval_map]
      rw [ih]
    · simp only [attach, Function.comp_apply, Fin.snoc_castSucc, eval_add_castSucc]
      exact congrFun ih j

lemma attach_width {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).1 = k + b.count := by
  have hw := (a.attach ρ b).2.1.width_eq
  rw [attach_count, ← Nat.add_assoc, ← a.width_eq] at hw
  exact hw

lemma attach_le {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    k ≤ (a.attach ρ b).1 := by rw [attach_width]; omega

lemma attach_preserve {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l)
    (x : Fin n → Bool) (i : Fin k) :
    (a.attach ρ b).2.1.eval x (i.castLE (a.attach_le ρ b)) = a.eval x i := by
  induction b with
  | input => rfl
  | add b o ih =>
    change ((a.attach ρ b).2.1.add (o.map (a.attach ρ b).2.2)).eval x
      (i.castLE (a.attach_le ρ b)).castSucc = _
    rw [eval_add_castSucc, ih]

/-- On fresh ancillas the compiled program realizes the network exactly,
including preservation of all unused wires. -/
lemma program_eval {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) (x : Basis q)
    (hfresh : ∀ i : Fin q, n ≤ i.val → x i = false) :
    (∀ i : Fin k, (BooleanProgram.eval (p.program h) x) (i.castLE h) =
      p.eval (fun j => x (j.castLE (p.input_le.trans h))) i) ∧
    (∀ i : Fin q, k ≤ i.val → (BooleanProgram.eval (p.program h) x) i = false) := by
  induction p with
  | input => exact ⟨fun _ => rfl, hfresh⟩
  | @add k p o ih =>
    have hk : k ≤ q := by omega
    obtain ⟨hpre, hrest⟩ := ih hk
    have hy : (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩ = false :=
      hrest _ (by simp)
    have hv : (o.compileOp h).value (BooleanProgram.eval (p.program hk) x) =
        o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk)))) := by
      rw [BoolNode.compileOp_value]
      congr 1
      funext i
      exact hpre i
    have heval : BooleanProgram.eval ((p.add o).program h) x =
        Function.update (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩
          (o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk))))) := by
      simp only [program, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (o.compileOp h).eval (BooleanProgram.eval (p.program hk) x) = _
      rw [BooleanOp.eval_fresh _ _ hy, hv]
      rfl
    rw [heval]
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [eval_add_last]
        exact Function.update_self _ _ _
      · rw [eval_add_castSucc]
        rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change j.val = k at hh; omega)]
        exact hpre j
    · intro i hi
      rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega)]
      exact hrest i (by omega)

end BoolNet

/-- Typed interfaces for network composition, with explicitly retained workspace. -/
structure BooleanNetwork (n m : ℕ) where
  width : ℕ
  net : BoolNet n width
  output : Fin m → Fin width


end ExactQuantumFactoring
end

end OAI
