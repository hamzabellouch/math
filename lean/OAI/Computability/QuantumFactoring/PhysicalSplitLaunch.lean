import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplit

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

lemma preparedOracle_encode_dependent {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : α→β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count≤r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=
      encodeState (f a) (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.1 ab.2))
      (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

namespace FixedSplit

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  packNet (work n)
    (packNet (PhysicalListSlots.work n) (select id) (Completion.zeros n (PhysicalListSlots.width n)))
    (Completion.zeros n (ordersWidth n))
lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=zero m := by
  simp only [initialNet,packNet_eval,eval_select,Function.comp_id,Completion.zeros_eval,zero]
lemma initialNet_count (n : ℕ) : (initialNet n).net.count=
    PhysicalListSlots.width n+PhysicalListSlots.work n+ordersWidth n+work n := by
  simp only [initialNet,packNet_count,count_select,Completion.zeros_count,zero_add]

/-- Runtime-modulus launch of the entire raw split. The circuit description
contains n only, never the input integer, its prime factors, or true orders. -/
abbrev launchWork (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+launchWork n
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
def launchEncoding {n : ℕ} (m : Basis n) (r : Raw n) : Basis (launchWidth n) :=
  packed (launchWork n) m (encoding m r)

theorem launch_state {n : ℕ} (m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (launchWork n) m (fun _=>false)))=
      encodeState (launchEncoding m) (fresh m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl

/-- Coherent correctness on an arbitrary retained history. A parameter-dependent
encoder keeps this run's actual modulus and all of its actual scratch registers. -/
theorem launch_on_history {α : Type*} [Fintype α] {p n r : ℕ}
    (e : α→Basis p) (ψ : α→ℂ) (m : BooleanNetwork p n)
    (hc : (m.comp (initialNet n)).net.count≤r) :
    (programMatrix (preparedOracle (m.comp (initialNet n)) hc (program n))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
      encodeState (fun ar : α×Raw n=>packed r (e ar.1) (encoding (m.eval (e ar.1)) ar.2))
        (RecordedHistory.appendState ψ (fun a=>fresh (m.eval (e a)))) := by
  apply preparedOracle_encode_dependent e (fun a=>encoding (m.eval (e a))) ψ
    (fun a=>fresh (m.eval (e a))) (m.comp (initialNet n)) hc (program n)
  intro a
  rw [eval_comp,initialNet_eval,program_state]

lemma launch_length (n : ℕ) : (launch n).length≤
    4*launchWork n+2*width n+(program n).length :=
  preparedOracle_length _ _ _

end FixedSplit
end ExactQuantumFactoring


end

end OAI
