import Mathlib
import OAI.Computability.QuantumFactoring.CyclicCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

def arrayConstant {n : ℕ} (s w : ℕ) (f : Fin s → ℕ) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => wordConstant (BitVec.ofNat w (f i)))

lemma arrayConstant_value {n s w : ℕ} (f : Fin s → ℕ) (x : Basis n) (i : Fin s) :
    (bitsValue (block ((arrayConstant s w f).eval x) i)).toNat = f i % 2^w := by
  rw [arrayConstant,wordBlocks_eval,wordConstant_eval,BitVec.toNat_ofNat]

lemma arrayConstant_count {n s w : ℕ} (f : Fin s → ℕ) :
    (arrayConstant (n := n) s w f).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  exact (wordConstant_count _).le

def cyclicOne {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then 1 else 0)

lemma cyclicOne_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicOne s w).eval x)=1 := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  ext i
  rw [decodeCyclic_coeff,cyclicOne,arrayConstant_value,AddMonoidAlgebra.one_def]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all [Nat.mod_eq_of_lt hp]

lemma cyclicOne_canonical {n s w m : ℕ} [NeZero s] (hm : 2 ≤ m) (x : Basis n) :
    CanonicalCyclic m ((cyclicOne s w).eval x) := by
  intro i
  rw [cyclicOne,arrayConstant_value]
  split_ifs
  · exact (Nat.mod_le _ _).trans_lt (by omega)
  · simp only [Nat.zero_mod]
    omega

def cyclicAddNet {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => addMod (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m)

lemma cyclicAddNet_value {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (i : Fin s) :
    (bitsValue (block ((cyclicAddNet a b m).eval x) i)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat+(bitsValue (block (b.eval x) i)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  rw [cyclicAddNet,wordBlocks_eval,addMod_value _ _ _ _ hm]
  simp only [eval_comp,blockNet_eval]

lemma cyclicAddNet_correct {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)+
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext i
  rw [decodeCyclic_coeff,cyclicAddNet_value _ _ _ _ hm]
  simp [ZMod.natCast_mod,decodeCyclic_coeff]

lemma cyclicAddNet_canonical {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicAddNet a b m).eval x) := by
  intro i
  rw [cyclicAddNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

lemma cyclicAddNet_count {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicAddNet a b m).net.count ≤
      s*w*(a.net.count+b.net.count+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  apply wordBlocks_count
  intro i
  have h := addMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m
  simpa only [count_comp,blockNet_count,add_zero] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
