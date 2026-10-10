import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalCompletionOutput
import OAI.Computability.QuantumFactoring.TensorWiring
import OAI.Computability.QuantumFactoring.PreparedOracle
import OAI.Computability.QuantumFactoring.TransitionNetworks
import OAI.Computability.QuantumFactoring.PhysicalListSlots

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace PhysicalListSlots

def sampleNet (n : ℕ) : BooleanNetwork (ListSampler.width n) n :=
  select (fun i => ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩)
lemma sampleNet_eval {n : ℕ} (x : Basis (ListSampler.width n)) : (sampleNet n).eval x=sampleRead x := rfl

def ordinaryNet (n : ℕ) : BooleanNetwork (ordinaryWidth n) (Completion.transitionWidth n) :=
  TransitionWords.encodeNet (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))
lemma ordinaryNet_eval {n : ℕ} (x : Basis (ordinaryWidth n)) : (ordinaryNet n).eval x=ordinary x := by
  change (TransitionWords.encodeNet _).eval x=TransitionWords.encode _
  rw [TransitionWords.encodeNet_eval]
  congr 1
  funext i
  rw [eval_comp,tensorSelect_inverse,sampleNet_eval]
lemma ordinaryNet_count (n : ℕ) : (ordinaryNet n).net.count ≤ Completion.transitionWidth n := by
  have h := TransitionWords.encodeNet_count
    (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))
    (c:=0) (by intro i; simp only [count_comp,tensorSelect,sampleNet,count_select]; omega)
  change (TransitionWords.encodeNet (fun i : Fin (n^5) =>
    (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))).net.count ≤ n*(n^5+1)
  simpa only [Nat.zero_add,Nat.mul_one] using h

def outputNet (n : ℕ) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  Completion.outputNet (ordinaryNet n) (2*n) (n*n^5)
lemma outputNet_eval {n : ℕ} (r : Result n) :
    (outputNet n).eval (layout n r)=output r := by
  change (Completion.outputNet _ _ _).eval (Completion.layout _ _ _ _ r)=_
  rw [Completion.outputNet_eval]
  unfold output Completion.output
  simp only [ordinaryNet_eval]
lemma outputNet_count (n : ℕ) : (outputNet n).net.count ≤
    8*Completion.transitionWidth n+194*n+21 := by
  have h := Completion.outputNet_count (ordinaryNet n) (2*n) (n*n^5)
  have hh := ordinaryNet_count n
  change (Completion.outputNet _ _ _).net.count ≤ _
  nlinarith

/-- Copy the runtime modulus into each literal sampler block; all other input
cells are zero. Only fixed wire placements and constants are used. -/
def singleZeroNet (n : ℕ) : BooleanNetwork n (ListSampler.width n) :=
  vector (fun i => if h : i.val<n then bit ⟨i.val,h⟩ else constant false)
lemma singleZeroNet_eval {n : ℕ} (m : Basis n) :
    (singleZeroNet n).eval m=ListSampler.word m (fun _=>false) (fun _=>false) := by
  funext i
  rw [singleZeroNet,eval_vector]
  by_cases h : i.val<n
  · rw [dite_eq_left h,eval_bit]
    unfold ListSampler.word
    rw [dite_eq_left h]
  · rw [dite_eq_right h,eval_constant]
    unfold ListSampler.word
    split_ifs <;> rfl
lemma singleZeroNet_count (n : ℕ) : (singleZeroNet n).net.count ≤ ListSampler.width n := by
  unfold singleZeroNet
  apply (count_vector_le _ (c:=1) ?_).trans (by omega)
  intro i
  by_cases h : i.val<n
  · rw [dite_eq_left h,count_bit]; omega
  · rw [dite_eq_right h,count_constant]

def ordinaryZeroNet (n : ℕ) : BooleanNetwork n (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5) => singleZeroNet n)
lemma ordinaryZeroNet_eval {n : ℕ} (m : Basis n) : (ordinaryZeroNet n).eval m=ordinaryZero m := by
  rw [ordinaryZeroNet,tensorNetwork_eval,ordinaryZero]
  congr 1
  funext i
  exact singleZeroNet_eval m
lemma ordinaryZeroNet_count (n : ℕ) : (ordinaryZeroNet n).net.count ≤ n^5*ListSampler.width n :=
  tensorNetwork_count_le _ (fun _ => singleZeroNet_count n)

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) (n*n^5)
lemma initialNet_eval {n : ℕ} (m : Basis n) : (initialNet n).eval m=layout n (zero m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl
lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤ n^5*ListSampler.width n+
    2*n+Completion.transitionWidth n+Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  omega

abbrev work (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+work n
/-- Length-uniform placement of the completed runtime-modulus list sampler. -/
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
lemma launch_state {n : ℕ} (m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (work n) m (fun _=>false)))=
      encodeState (fun r : Result n => packed (work n) m (layout n r)) (fresh m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl
lemma launch_length (n : ℕ) : (launch n).length ≤
    4*work n+2*width n+(program n).length := preparedOracle_length _ _ _

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
