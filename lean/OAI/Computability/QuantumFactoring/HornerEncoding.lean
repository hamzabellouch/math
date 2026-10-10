import Mathlib
import OAI.Computability.QuantumFactoring.Basic
import OAI.Computability.QuantumFactoring.BitNumbers
import OAI.Computability.QuantumFactoring.ModularPower
import OAI.Computability.QuantumFactoring.TriangularAlgebra

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BitArithmetic

lemma horner_sum {b : ℕ} (e : Basis b) (k : ℕ) (hk : k ≤ b) :
    horner e k hk = ∑ i : Fin k, 2^(k-1-i.val)*(e (i.castLE hk)).toNat := by
  induction k with
  | zero => simp [horner]
  | succ k ih =>
    rw [horner,ih (by omega),Fin.sum_univ_castSucc,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : k+1-1-i.val = (k-1-i.val)+1 := by have := i.isLt; omega
      rw [show (i.castSucc : Fin (k+1)).val = i.val from rfl,he,pow_succ]
      have hi : ((i.castSucc).castLE hk) = i.castLE (by omega : k ≤ b) := Fin.ext rfl
      rw [hi]
      ring
    · simp only [Fin.val_last,Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul]
      rfl

lemma horner_full {b : ℕ} (e : Basis b) :
    horner e b le_rfl = Triangular.inputNumber e := by
  rw [horner_sum]
  rfl

end BitArithmetic

lemma Triangular.outputNumber_value {b : ℕ} (x : Basis b) :
    outputNumber x = (bitsValue x).toNat := (bitsValue_toNat x).symm

/-- The physical input word reversal is an explicit wire permutation. -/
def reverseBits (b : ℕ) : Equiv.Perm (Basis b) where
  toFun x := x ∘ Fin.rev
  invFun x := x ∘ Fin.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma Triangular.inputNumber_reverse {b : ℕ} (x : Basis b) :
    inputNumber x = (bitsValue (reverseBits b x)).toNat := by
  rw [bitsValue_toNat]
  unfold inputNumber
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin b))]
  apply Finset.sum_congr rfl
  intro i _
  change 2^(b-1-(b-(i.val+1)))*(x (Fin.rev i)).toNat =
    2^i.val*(x (Fin.rev i)).toNat
  have he : b-1-(b-(i.val+1)) = i.val := by have := i.isLt; omega
  rw [he]

lemma Triangular.inputNumber_lt {b : ℕ} (x : Basis b) : inputNumber x < 2^b := by
  rw [inputNumber_reverse]
  exact (bitsValue _).isLt

lemma Triangular.inputNumber_bijective (b : ℕ) :
    Function.Bijective (fun x : Basis b =>
      (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) := by
  have h := (bitsEquiv b).bijective.comp (reverseBits b).bijective
  have he : (fun x : Basis b => (⟨inputNumber x,inputNumber_lt x⟩ : Fin (2^b))) =
    fun x => ((bitsEquiv b (reverseBits b x)).toFin) := by
    funext x
    apply Fin.ext
    exact inputNumber_reverse x
  rw [he]
  exact (BitVec.equivFin (m := b)).bijective.comp h

end ExactQuantumFactoring


end

end OAI
