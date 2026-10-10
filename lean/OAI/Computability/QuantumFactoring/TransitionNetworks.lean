import Mathlib
import OAI.Computability.QuantumFactoring.TransitionWords

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
namespace TransitionWords

/-- Each field is wired into its fixed source layout, and the final unused word
is explicitly zeroed. The cap K and all placements are independent of inputs. -/
def encodeNet {k n K : ℕ} (f : Fin K → BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  vector (fun i =>
    let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
    if h : j.1.val<K then (f ⟨j.1.val,h⟩).rewire (fun _ => j.2) else constant false)

lemma encodeNet_eval {k n K : ℕ} (f : Fin K → BooleanNetwork k n) (x : Basis k) :
    (encodeNet f).eval x=encode (fun i => (f i).eval x) := by
  funext i
  rw [encodeNet,eval_vector]
  dsimp only [encode]
  split_ifs <;> simp only [eval_rewire,Function.comp_apply,eval_constant]

lemma encodeNet_count {k n K c : ℕ} (f : Fin K → BooleanNetwork k n)
    (hf : ∀ i,(f i).net.count ≤ c) : (encodeNet f).net.count ≤ n*(K+1)*(c+1) := by
  apply count_vector_le
  intro i
  dsimp only
  split_ifs with h
  · rw [dite_eq_left h,count_rewire]
    exact (hf _).trans (Nat.le_add_right _ _)
  · rw [dite_eq_right h]
    change 1 ≤ c+1
    omega

end TransitionWords
end ExactQuantumFactoring


end

end OAI
