import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeLaunch
import OAI.Computability.QuantumFactoring.PhysicalMachineMass

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeKernel
abbrev width (n : ℕ) := PhysicalNode.runWidth n
abbrev Raw (n : ℕ) := SplitMachine.Trace n (2*n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) := PhysicalNode.runInitial n
def start {n : ℕ} (q : Basis n) := (PhysicalNode.startNet n).eval q
def zero {n : ℕ} (q : Basis n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).initial (2*n) (start q)
def encoding {n : ℕ} (q : Basis n) (r : Raw n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).encoded (start q) (2*n) r
noncomputable def fresh {n : ℕ} (q : Basis n) (r : Raw n) : ℂ :=
  (PhysicalNode.machine n (2*n)).state (start q) (2*n) r
def program (n : ℕ) : List (Instruction (width n)) :=
  (PhysicalNode.machine n (2*n)).program (2*n)
noncomputable def passed {n : ℕ} (q : Basis n) (r : Raw n) : Prop :=
  (PhysicalNode.machine n (2*n)).passed (start q) (2*n) r
lemma initialNet_eval {n : ℕ} (q : Basis n) : (initialNet n).eval q=zero q := by
  rw [initialNet,PhysicalNode.runInitial,eval_comp,SplitMachine.initialNet_eval]
  rfl
lemma program_state {n : ℕ} (q : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (zero q))=encodeState (encoding q) (fresh q) :=
  (PhysicalNode.machine n (2*n)).program_state (start q) (2*n)
lemma encoding_injective {n : ℕ} (q : Basis n) : Function.Injective (encoding q) :=
  (PhysicalNode.machine n (2*n)).encoded_injective (start q) (2*n)
lemma fresh_normalized {n : ℕ} (q : Basis n) : ∑ r,Complex.normSq (fresh q r)=1 :=
  (PhysicalNode.machine n (2*n)).state_normalized (start q) (2*n)
lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (q : Basis n) :
    Exactness.outcomeMass (passed q) (fresh q)=
      ((Completion.target n:ℝ)^(n^5+1))^(2*n) :=
  (PhysicalNode.machine n (2*n)).passed_mass hn (start q) (2*n)
end NodeKernel
end ExactQuantumFactoring


end

end OAI
