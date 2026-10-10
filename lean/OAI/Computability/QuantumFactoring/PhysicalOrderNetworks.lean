import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalOrderSlots
import OAI.Computability.QuantumFactoring.PhysicalCompletionOutput
import OAI.Computability.QuantumFactoring.TensorWiring
import OAI.Computability.QuantumFactoring.PreparedOracle

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma packed_append {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y=Fin.append (Fin.append x y) (fun _=>false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · exact (packed_input x y j).trans (by simp)
    · exact (packed_target x y j).trans (by simp)
  · rw [packed_work x y _ (by simp),Fin.append_right]

namespace BooleanNetwork

def packNet {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    BooleanNetwork k (n+m+r) := (a.pair b).pair (Completion.zeros k r)
lemma packNet_eval {k n m r : ℕ} (a : BooleanNetwork k n) (b : BooleanNetwork k m)
    (x : Basis k) : (packNet r a b).eval x=packed r (a.eval x) (b.eval x) := by
  rw [packNet,eval_pair,eval_pair,Completion.zeros_eval,packed_append]
lemma packNet_count {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    (packNet r a b).net.count=a.net.count+b.net.count+r := by
  simp only [packNet,count_pair,Completion.zeros_count]

end BooleanNetwork
lemma append_false (n m : ℕ) : Fin.append (fun _ : Fin n=>false) (fun _ : Fin m=>false)=fun _=>false := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only [Fin.append_left,Fin.append_right]

namespace OrderSlots

lemma triangular_zero (b : ℕ) : Triangular.encode b ((fun _=>false),0)=fun _=>false := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  dsimp [Triangular.encode]
  rw [h,packed_append]
  simp only [append_false]

def samplerZeroNet (w b : ℕ) : BooleanNetwork (w+w) (OrderSample.width w b) :=
  packNet (OrderSample.scratch w b)
    ((select id).pair (Completion.zeros (w+w) (Triangular.width b))) (Completion.zeros (w+w) w)
lemma samplerZeroNet_eval {w b : ℕ} (a m : Basis w) :
    (samplerZeroNet w b).eval (Fin.append a m)=OrderSample.word a m (fun _=>false) (fun _=>false) := by
  rw [samplerZeroNet,packNet_eval,eval_pair,eval_select,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Function.comp_id,OrderSample.word,OrderSample.inputWord,triangular_zero]
lemma samplerZeroNet_count (w b : ℕ) :
    (samplerZeroNet w b).net.count=Triangular.width b+w+OrderSample.scratch w b := by
  simp only [samplerZeroNet,packNet_count,count_pair,count_select,Completion.zeros_count,zero_add]

def rawZeroNet (n : ℕ) : BooleanNetwork (n+n) (OrderTrial.rawWidth n (sampleExponent n) n) :=
  (Completion.zeros (n+n) 2).pair
    ((samplerZeroNet n (sampleExponent n+2)).pair (Completion.zeros (n+n) (OrderTrial.guessWidth n)))
lemma rawZeroNet_eval {n : ℕ} (a m : Basis n) :
    (rawZeroNet n).eval (Fin.append a m)=
      OrderTrial.rawLayout n (sampleExponent n) n (OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [rawZeroNet,eval_pair,eval_pair,Completion.zeros_eval,Completion.zeros_eval,samplerZeroNet_eval]
  simp only [OrderTrial.rawLayout,productLayout_apply,Equiv.refl_apply,OrderTrial.rawZero,
    OrderTrial.guessLayout,OrderTrial.guessZero]
  simp only [append_false]
lemma rawZeroNet_count (n : ℕ) :
    (rawZeroNet n).net.count ≤ OrderTrial.rawWidth n (sampleExponent n) n := by
  simp only [rawZeroNet,count_pair,Completion.zeros_count,samplerZeroNet_count]
  dsimp [OrderTrial.rawWidth,OrderSample.width,OrderSample.inputWidth]
  omega

def ordinaryZeroNet (n : ℕ) : BooleanNetwork (n+n) (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5)=>rawZeroNet n)
lemma ordinaryZeroNet_eval {n : ℕ} (a m : Basis n) :
    (ordinaryZeroNet n).eval (Fin.append a m)=ordinaryLayout n (fun _=>OrderTrial.rawZero (sampleExponent n) n a m) := by
  rw [ordinaryZeroNet,tensorNetwork_eval]
  simp only [rawZeroNet_eval,ordinaryLayout,Equiv.trans_apply]
  rfl
lemma ordinaryZeroNet_count (n : ℕ) :
    (ordinaryZeroNet n).net.count ≤ n^5*OrderTrial.rawWidth n (sampleExponent n) n :=
  tensorNetwork_count_le _ (fun _=>rawZeroNet_count n)

def initialNet (n : ℕ) : BooleanNetwork (n+n) (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)
lemma initialNet_eval {n : ℕ} (a m : Basis n) :
    (initialNet n).eval (Fin.append a m)=layout n (zero a m) := by
  rw [initialNet,Completion.initialNet_eval,ordinaryZeroNet_eval]
  rfl
lemma initialNet_count (n : ℕ) : (initialNet n).net.count ≤
    n^5*OrderTrial.rawWidth n (sampleExponent n) n+2*n+Completion.transitionWidth n+coinWidth n := by
  rw [initialNet,Completion.initialNet_count]
  have h := ordinaryZeroNet_count n
  dsimp only [coinWidth]
  omega

abbrev work (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := (n+n)+width n+work n
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)
lemma launch_state {n : ℕ} (a m : Basis n) :
    (programMatrix (launch n)).mulVec (basisVector (packed (work n) (Fin.append a m) (fun _=>false)))=
      encodeState (fun r : Result n=>packed (work n) (Fin.append a m) (layout n r)) (fresh n a m) := by
  rw [launch,preparedOracle_basis,initialNet_eval,program_state,encodeState_comp]
  rfl
lemma launch_length (n : ℕ) : (launch n).length ≤4*work n+2*width n+(program n).length :=
  preparedOracle_length _ _ _

end OrderSlots
end ExactQuantumFactoring


end

end OAI
