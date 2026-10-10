import Mathlib
import OAI.Computability.QuantumFactoring.BooleanNetwork

namespace OAI

section
namespace ExactQuantumFactoring

namespace BooleanNetwork

def eval {n m : ℕ} (c : BooleanNetwork n m) (x : Fin n → Bool) : Fin m → Bool :=
  c.net.eval x ∘ c.output

def select {n m : ℕ} (f : Fin m → Fin n) : BooleanNetwork n m := ⟨n, .input, f⟩

def node {n : ℕ} (o : BoolNode n) : BooleanNetwork n 1 :=
  ⟨n+1, .add .input o, fun _ => Fin.last n⟩

def comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) : BooleanNetwork n l :=
  let c := a.net.attach a.output b.net
  ⟨c.1, c.2.1, c.2.2 ∘ b.output⟩

lemma eval_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l)
    (x : Fin n → Bool) : (a.comp b).eval x = b.eval (a.eval x) := by
  change ((a.net.attach a.output b.net).2.1.eval x ∘ (a.net.attach a.output b.net).2.2) ∘
    b.output = _
  rw [BoolNet.attach_eval]
  rfl

lemma count_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    (a.comp b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

/-- Parallel computations share the input but retain disjoint new traces. -/
def pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) : BooleanNetwork n (m+l) :=
  let ρ : Fin n → Fin a.width := fun i => i.castLE a.net.input_le
  let c := a.net.attach ρ b.net
  ⟨c.1, c.2.1, Fin.append (fun i => (a.output i).castLE (a.net.attach_le ρ b.net))
    (c.2.2 ∘ b.output)⟩

lemma eval_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l)
    (x : Fin n → Bool) : (a.pair b).eval x = Fin.append (a.eval x) (b.eval x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pair, eval, Function.comp_apply, Fin.append_left]
    exact BoolNet.attach_preserve _ _ _ _ _
  · simp only [pair, eval, Function.comp_apply, Fin.append_right]
    have he := congrFun (BoolNet.attach_eval a.net (fun i => i.castLE a.net.input_le) b.net x) (b.output j)
    have hi : a.net.eval x ∘ (fun i : Fin n => i.castLE a.net.input_le) = x := by
      funext j
      exact BoolNet.eval_input _ _ _
    rw [hi] at he
    exact he

lemma count_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    (a.pair b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

@[simp] lemma eval_select {n m : ℕ} (f : Fin m → Fin n) (x : Fin n → Bool) :
    (select f).eval x = x ∘ f := rfl

@[simp] lemma count_select {n m : ℕ} (f : Fin m → Fin n) :
    (select f).net.count = 0 := rfl

@[simp] lemma eval_node {n : ℕ} (o : BoolNode n) (x : Fin n → Bool) (i : Fin 1) :
    (node o).eval x i = o.eval x := by
  exact BoolNet.eval_add_last _ _ _

@[simp] lemma count_node {n : ℕ} (o : BoolNode n) : (node o).net.count = 1 := rfl

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
