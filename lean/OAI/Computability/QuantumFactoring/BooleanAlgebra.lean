import Mathlib
import OAI.Computability.QuantumFactoring.BooleanNetworkFurther

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

/-- Wire routing is free: it refers to values already physically present. -/
def rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) : BooleanNetwork n l :=
  ⟨c.width, c.net, c.output ∘ f⟩

@[simp] lemma eval_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m)
    (x : Fin n → Bool) : (c.rewire f).eval x = c.eval x ∘ f := rfl

@[simp] lemma count_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) :
    (c.rewire f).net.count = c.net.count := rfl

def bit {n : ℕ} (i : Fin n) : BooleanNetwork n 1 := select (fun _ => i)
def constant {n : ℕ} (b : Bool) : BooleanNetwork n 1 := node (.constant b)
def bnot {n : ℕ} (a : BooleanNetwork n 1) : BooleanNetwork n 1 := a.comp (node (.neg 0))
def band {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.pair b).comp (node (.conj 0 1))
def bor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 := (a.bnot.band b.bnot).bnot
def bxor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.band b.bnot).bor (a.bnot.band b)
def mux {n : ℕ} (c a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (c.band a).bor (c.bnot.band b)
def majority {n : ℕ} (a b c : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.band b).bor (c.band (a.bor b))

@[simp] lemma eval_bit {n : ℕ} (i : Fin n) (x : Fin n → Bool) (j : Fin 1) :
    (bit i).eval x j = x i := rfl

@[simp] lemma eval_constant {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : Fin 1) :
    (constant b).eval x j = b := eval_node _ _ _

@[simp] lemma eval_bnot {n : ℕ} (a : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    a.bnot.eval x j = !(a.eval x 0) := by simp [bnot, eval_comp, BoolNode.eval]

@[simp] lemma eval_band {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.band b).eval x j = (a.eval x 0 && b.eval x 0) := by
  simp only [band, eval_comp, eval_node, BoolNode.eval, eval_pair]
  rfl

@[simp] lemma eval_bor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bor b).eval x j = (a.eval x 0 || b.eval x 0) := by
  simp [bor]

@[simp] lemma eval_bxor {n : ℕ} (a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (a.bxor b).eval x j = Bool.xor (a.eval x 0) (b.eval x 0) := by
  simp only [bxor, eval_bor, eval_band, eval_bnot]
  cases a.eval x 0 <;> cases b.eval x 0 <;> rfl

@[simp] lemma eval_mux {n : ℕ} (c a b : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (mux c a b).eval x j = if c.eval x 0 then a.eval x 0 else b.eval x 0 := by
  simp only [mux, eval_bor, eval_band, eval_bnot]
  cases c.eval x 0 <;> simp

@[simp] lemma eval_majority {n : ℕ} (a b c : BooleanNetwork n 1) (x : Fin n → Bool) (j : Fin 1) :
    (majority a b c).eval x j = Bool.atLeastTwo (a.eval x 0) (b.eval x 0) (c.eval x 0) := by
  simp only [majority, eval_bor, eval_band]
  cases a.eval x 0 <;> cases b.eval x 0 <;> cases c.eval x 0 <;> rfl

@[simp] lemma count_bit {n : ℕ} (i : Fin n) : (bit i).net.count = 0 := rfl
@[simp] lemma count_constant {n : ℕ} (b : Bool) : (constant (n := n) b).net.count = 1 := rfl
@[simp] lemma count_bnot {n : ℕ} (a : BooleanNetwork n 1) : a.bnot.net.count = a.net.count + 1 := by
  simp [bnot, count_comp]
@[simp] lemma count_band {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.band b).net.count = a.net.count + b.net.count + 1 := by simp [band, count_comp, count_pair]
@[simp] lemma count_bor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bor b).net.count = a.net.count + b.net.count + 4 := by simp [bor]; omega
@[simp] lemma count_bxor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bxor b).net.count = 2 * a.net.count + 2 * b.net.count + 8 := by simp [bxor]; omega
@[simp] lemma count_mux {n : ℕ} (c a b : BooleanNetwork n 1) :
    (mux c a b).net.count = 2 * c.net.count + a.net.count + b.net.count + 7 := by simp [mux]; omega
@[simp] lemma count_majority {n : ℕ} (a b c : BooleanNetwork n 1) :
    (majority a b c).net.count = 2 * a.net.count + 2 * b.net.count + c.net.count + 10 := by
  simp [majority]; omega

/-- Logical assignment preserves the input values in the physical trace, but
provides the standard overwritten-state interface to the next computation. -/
def assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) : BooleanNetwork n n :=
  ((select id).pair v).rewire (fun j => if j = i then Fin.natAdd n 0 else j.castAdd 1)

lemma eval_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) (x : Fin n → Bool) :
    (assign i v).eval x = Function.update x i (v.eval x 0) := by
  funext j
  simp only [assign, eval_rewire, Function.comp_apply, eval_pair, eval_select]
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

@[simp] lemma count_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) :
    (assign i v).net.count = v.net.count := by simp [assign, count_pair]

/-- Sequentially composed bounded logical updates compile by retained history. -/
def sequence {n : ℕ} : List (BooleanNetwork n n) → BooleanNetwork n n
  | [] => select id
  | c :: cs => c.comp (sequence cs)

lemma eval_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) (x : Fin n → Bool) :
    (sequence cs).eval x = cs.foldl (fun x c => c.eval x) x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => rw [sequence, eval_comp, ih]; rfl

lemma count_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) :
    (sequence cs).net.count = (cs.map (fun c => c.net.count)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sequence, count_comp, ih]

def iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) : BooleanNetwork n n :=
  sequence (List.replicate k c)

lemma eval_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) (x : Fin n → Bool) :
    (iterate c k).eval x = (c.eval^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (c.comp (iterate c k)).eval x = _
    rw [eval_comp, ih, Function.iterate_succ_apply]

lemma count_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) :
    (iterate c k).net.count = k * c.net.count := by
  simp [iterate, count_sequence, List.sum_replicate]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
