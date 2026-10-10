import Mathlib
import OAI.Computability.QuantumFactoring.InitialOrderState
import OAI.Computability.QuantumFactoring.FactorGuess
import OAI.Computability.QuantumFactoring.MaskedPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BitArithmetic BooleanNetwork

/-- Compute ceil-log activation bits by bounded comparisons. The constant
2^i fits n bits, and the circuit is polynomial on invalid inputs too. -/
def listMaskNet (n : ℕ) : BooleanNetwork n n :=
  vector (fun i : Fin n => wordLt (wordConstant (BitVec.ofNat n (2^i.val))) (select id))

lemma listMaskNet_eval (n : ℕ) (m : Basis n) :
    (listMaskNet n).eval m=prefixMask n (Nat.clog 2 (bitsValue m).toNat) := by
  funext i
  have hp : 2^i.val<2^n := Nat.pow_lt_pow_right (by decide) i.isLt
  simp only [listMaskNet,eval_vector,wordLt_eval,wordConstant_eval,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp,eval_select,Function.comp_id,prefixMask]
  congr 1
  exact propext (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).symm

lemma listMaskNet_count (n : ℕ) : (listMaskNet n).net.count ≤ n*(49*n+8) := by
  apply count_vector_le
  intro i
  have hh := wordLt_count (wordConstant (n:=n) (BitVec.ofNat n (2^i.val))) (select id)
  simp only [wordConstant_count,count_select,add_zero] at hh
  omega

def padBits {b n : ℕ} (_h : b ≤ n) (x : Basis b) : Basis n :=
  fun i => if hi : i.val<b then x ⟨i.val,hi⟩ else false

lemma padBits_at {b n : ℕ} (h : b ≤ n) (x : Basis b) (i : Fin b) :
    padBits h x (i.castLE h)=x i := by
  simp [padBits,i.isLt]

lemma padBits_injective {b n : ℕ} (h : b ≤ n) : Function.Injective (padBits h) := by
  intro x y hh
  funext i
  have he := congrFun hh (i.castLE h)
  simpa only [padBits_at] using he

lemma padBits_range {b n : ℕ} (h : b ≤ n) (y : Basis n) :
    y∈Set.range (padBits h) ↔ ∀ i : Fin n,b ≤ i.val→y i=false := by
  constructor
  · rintro ⟨x,rfl⟩ i hi
    simp [padBits,Nat.not_lt.mpr hi]
  · intro hh
    refine ⟨fun i => y (i.castLE h),?_⟩
    funext i
    unfold padBits
    split_ifs with hi
    · rfl
    · exact (hh i (by omega)).symm

lemma prefixFair_encode {b n : ℕ} (hb : b ≤ n) :
    (fun y : Basis n => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0)=
      encodeState (padBits hb) (fairState b) := by
  classical
  funext y
  by_cases hy : y∈Set.range (padBits hb)
  · obtain ⟨x,rfl⟩ := hy
    rw [encodeState_at _ (padBits_injective hb),ite_eq_left ((padBits_range hb _).mp ⟨x,rfl⟩)]
    rfl
  · rw [encodeState_outside _ _ y hy,ite_eq_right (fun hh => hy ((padBits_range hb y).mpr hh))]

/-- Runtime active-width preparation, stated as an exact physical program
column over the source's b=ceil(log₂m) fair state. -/
lemma maskedList_state (n : ℕ) (m : Basis n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append ((listMaskNet n).eval m) (fun _ => false)))=
      encodeState (fun y => Fin.append ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
        (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [listMaskNet_eval,maskedPrefix_zero _ _ (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),
    prefixFair_encode (Nat.clog_le_of_le_pow (bitsValue m).isLt.le),encodeState_comp]
  rfl

lemma padBits_value {b n : ℕ} (hb : b ≤ n) (x : Basis b) :
    (bitsValue (padBits hb x)).toNat=(bitsValue x).toNat := by
  have he : bitsValue (padBits hb x)=(bitsValue x).setWidth n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (padBits hb x)).getLsbD i=padBits hb x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
      BitVec.getLsbD_setWidth]
    simp only [hi,decide_true,Bool.true_and,padBits]
    split_ifs with hib
    · exact (bitsValue_bit x ⟨i,hib⟩).symm
    · exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
  rw [he,setWidth_toNat_of_le hb]

end ExactQuantumFactoring


end

end OAI
