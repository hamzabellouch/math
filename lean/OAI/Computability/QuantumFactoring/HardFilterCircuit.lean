import Mathlib
import OAI.Computability.QuantumFactoring.SuppliedDivisorCircuit
import OAI.Computability.QuantumFactoring.UniversalSplit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace UniversalSplit

def hardOn {k n : ℕ} (m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  ((wordLe (wordConstant (BitVec.ofNat n 2)) m).band (m.comp (primeWord n)).bnot).band
    ((evenOn m).bnot.band ((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).bnot)

lemma hardOn_value {k n : ℕ} (hn : 128≤n) (m : BooleanNetwork k n) (x : Basis k) :
    (hardOn m).eval x 0=true ↔ Hard (bitsValue (m.eval x)).toNat := by
  have hf : 2<2^n := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega : 2≤n))
  have hp : (((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).eval x 0=true) ↔
      Primality.PerfectPower (bitsValue (m.eval x)).toNat := by
    rw [eval_comp,perfectPowerNet_correct (by omega)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
    · rw [eval_comp,resizeWord_toNat (rootWidth_ge n)]
      exact (bitsValue (m.eval x)).isLt
  rw [hardOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLe_eval,decide_eq_true_eq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf,
    bnot_value,eval_comp,primeWord_value hn,eval_band,Bool.and_eq_true,bnot_value,
    evenOn_value (by omega),bnot_value,hp]
  rw [←even_iff_two_dvd,Nat.not_even_iff_odd]
  exact and_assoc
end UniversalSplit
end ExactQuantumFactoring


end

end OAI
