import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplit
import OAI.Computability.QuantumFactoring.PhysicalOrderDecoder
import OAI.Computability.QuantumFactoring.WideSplitCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace FixedSplit

def launchWires (n : ℕ) : BooleanNetwork (width n) (PhysicalListSlots.launchWidth n) :=
  select (firstRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def allOrderWires (n : ℕ) : BooleanNetwork (width n) (ordersWidth n) :=
  select (targetRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def modulusNet (n : ℕ) : BooleanNetwork (width n) n := (launchWires n).comp (modulusWires n)
def actualBaseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) n :=
  (launchWires n).comp (baseNet i)
def actualOrderRawNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (OrderSlots.width n) :=
  (allOrderWires n).comp (tensorSelect (OrderSlots.width n) (n^5) i)
def actualOrderNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  OrderSlots.outputOn (actualBaseNet i) (modulusNet n) (actualOrderRawNet i)

lemma launchWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (launchWires n).eval (encoding m r)=listEncoding m r.1 := packed_first _ _
lemma allOrderWires_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (allOrderWires n).eval (encoding m r)=ordersLayout n r.2 := packed_targetRegister _ _
lemma modulusNet_eval {n : ℕ} (m : Basis n) (r : Raw n) :
    (modulusNet n).eval (encoding m r)=m := by
  rw [modulusNet,eval_comp,launchWires_eval,modulusWires_eval]
lemma actualBaseNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualBaseNet i).eval (encoding m r)=bases r.1 i := by
  rw [actualBaseNet,eval_comp,launchWires_eval,baseNet_eval]
lemma actualOrderRawNet_eval {n : ℕ} (i : Fin (n^5)) (m : Basis n) (r : Raw n) :
    (actualOrderRawNet i).eval (encoding m r)=OrderSlots.layout n (r.2 i) := by
  rw [actualOrderRawNet,eval_comp,allOrderWires_eval]
  exact tensorSelect_eval _ i
lemma actualOrderNet_eval {n : ℕ} (hn : 1≤n) (i : Fin (n^5)) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (actualOrderNet i).eval (encoding m r)=OrderSlots.output (bases r.1 i) m (r.2 i) := by
  rw [actualOrderNet,OrderSlots.outputOn_eval _ _ _ _ (r.2 i)
    (actualOrderRawNet_eval i m r) hn (by rw [modulusNet_eval];exact hm),
    actualBaseNet_eval,modulusNet_eval]

def liftedModulus (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  (modulusNet n).comp (resizeWord n (n+1))
def actualPairs (n : ℕ) : List (BooleanNetwork (width n) (n+1) ×
    BooleanNetwork (width n) (Completion.transitionWidth n)) :=
  List.ofFn (fun i : Fin (n^5) => ((actualBaseNet i).comp (resizeWord n (n+1)),actualOrderNet i))

/-- Supplied divisor computed from exactly this run's retained quantum bits.
All guarded arithmetic is explicit, including full rare-branch order guesses. -/
def divisorNet (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  suppliedBits n (liftedModulus n) (actualPairs n)

theorem divisorNet_value {n : ℕ} (hn : 2≤n) (m : Basis n) (r : Raw n)
    (hm : 2≤(bitsValue m).toNat) :
    (bitsValue ((divisorNet n).eval (encoding m r))).toNat=divisor m r := by
  have hm' : (bitsValue ((liftedModulus n).eval (encoding m r))).toNat=(bitsValue m).toNat := by
    rw [liftedModulus,eval_comp,resizeWord_toNat (by omega),modulusNet_eval]
  have he : 2≤Completion.transitionWidth n := by
    unfold Completion.transitionWidth
    calc 2≤n := hn
         _ ≤ n*(n^5+1) := Nat.le_mul_of_pos_right n (by omega)
  rw [divisorNet,suppliedBits_value (by omega) he _ _ _ (by rw [hm'];exact hm)
    (by rw [hm'];exact (bitsValue m).isLt),hm',divisor]
  congr 1
  rw [actualPairs,List.map_ofFn]
  unfold pairs
  congr 1
  funext i
  simp only [Function.comp_apply,eval_comp,resizeWord_toNat (Nat.le_succ n),
    actualBaseNet_eval,actualOrderNet_eval (by omega : 1≤n) i m r hm]

end FixedSplit
end ExactQuantumFactoring


end

end OAI
