import Mathlib
import OAI.Computability.QuantumFactoring.TensorPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def tensorWire (q : ℕ) : (K : ℕ) → Fin K → Fin q → Fin (tensorWidth q K)
  | 0, i => Fin.elim0 i
  | K+1, i => Fin.cases (fun j => j.castAdd (tensorWidth q K))
      (fun i j => Fin.natAdd q (tensorWire q K i j)) i

lemma tensorLayout_wire {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) (j : Fin q) :
    tensorLayout q K x (tensorWire q K i j)=x i j := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x)) (j.castAdd _) = _
      exact Fin.append_left _ _ _
    · change Fin.append (x 0) (tensorLayout q K (Fin.tail x))
        (Fin.natAdd q (tensorWire q K i j)) = _
      rw [Fin.append_right]
      exact ih (Fin.tail x) i

def tensorSelect (q K : ℕ) (i : Fin K) : BooleanNetwork (tensorWidth q K) q :=
  select (tensorWire q K i)
lemma tensorSelect_eval {q K : ℕ} (x : Fin K → Basis q) (i : Fin K) :
    (tensorSelect q K i).eval (tensorLayout q K x)=x i := by
  funext j
  exact tensorLayout_wire x i j
lemma tensorSelect_inverse {q K : ℕ} (x : Basis (tensorWidth q K)) (i : Fin K) :
    (tensorSelect q K i).eval x=(tensorLayout q K).symm x i := by
  obtain ⟨y,rfl⟩ := (tensorLayout q K).surjective x
  rw [tensorSelect_eval,Equiv.symm_apply_apply]

/-- Direct concatenation prepares K fixed blocks. No branch-indexed truth table
is allocated; the count is the sum of the supplied K finite networks. -/
def tensorNetwork {n q : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork n q) →
    BooleanNetwork n (tensorWidth q K)
  | 0,_ => select Fin.elim0
  | _K+1,f => (f 0).pair (tensorNetwork (fun i => f i.succ))
lemma tensorNetwork_eval {n q K : ℕ} (f : Fin K → BooleanNetwork n q) (x : Basis n) :
    (tensorNetwork f).eval x=tensorLayout q K (fun i => (f i).eval x) := by
  induction K with
  | zero => exact Subsingleton.elim _ _
  | succ K ih => rw [tensorNetwork,eval_pair,ih,tensorLayout_succ]; rfl
lemma tensorNetwork_count {n q K : ℕ} (f : Fin K → BooleanNetwork n q) :
    (tensorNetwork f).net.count=∑ i,(f i).net.count := by
  induction K with
  | zero => simp [tensorNetwork]
  | succ K ih => simp only [tensorNetwork,count_pair,ih,Fin.sum_univ_succ]
lemma tensorNetwork_count_le {n q K c : ℕ} (f : Fin K → BooleanNetwork n q)
    (hf : ∀ i,(f i).net.count ≤ c) : (tensorNetwork f).net.count ≤ K*c := by
  rw [tensorNetwork_count]
  calc
    _ ≤ ∑ _ : Fin K,c := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp

end ExactQuantumFactoring


end

end OAI
