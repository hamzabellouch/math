import Mathlib
import OAI.Computability.QuantumFactoring.ModularMultiply

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

abbrev powerWidth (w b : ℕ) := ((w+w)+b)+w

def powerPack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    Basis (powerWidth w b) := Fin.append (Fin.append (Fin.append a m) e) z

def powerBase (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd w)
def powerModulus (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (fun i => ((Fin.natAdd w i).castAdd b).castAdd w)
def powerAcc (w b : ℕ) : BooleanNetwork (powerWidth w b) w :=
  select (Fin.natAdd ((w+w)+b))
def powerBit (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) 1 :=
  bit ((Fin.natAdd (w+w) i).castAdd w)

@[simp] lemma powerBase_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerBase w b).eval (powerPack a m e z) = a := by
  funext i
  simp only [powerBase, eval_select, Function.comp_apply, powerPack, Fin.append_left]
@[simp] lemma powerModulus_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerModulus w b).eval (powerPack a m e z) = m := by
  funext i
  simp only [powerModulus, eval_select, Function.comp_apply, powerPack, Fin.append_left,
    Fin.append_right]
@[simp] lemma powerAcc_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    (powerAcc w b).eval (powerPack a m e z) = z := by
  funext i
  simp only [powerAcc, eval_select, Function.comp_apply, powerPack, Fin.append_right]
@[simp] lemma powerBit_eval {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerBit w i).eval (powerPack a m e z) 0 = e i := by
  simp only [powerBit, eval_bit, powerPack, Fin.append_left, Fin.append_right]

def powerNew (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) w :=
  let sq := mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)
  wordMux (powerBit w i) (mulMod sq (powerBase w b) (powerModulus w b)) sq

def powerStep (w : ℕ) {b : ℕ} (i : Fin b) :
    BooleanNetwork (powerWidth w b) (powerWidth w b) :=
  (select (Fin.castAdd w)).pair (powerNew w i)

lemma powerNew_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerNew w i).net.count ≤ 3*(1224*w*w+143*w+12)+7*w := by
  have h₁ := mulMod_count (powerAcc w b) (powerAcc w b) (powerModulus w b)
  have h₂ := mulMod_count
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (powerBase w b) (powerModulus w b)
  have h₀ : (powerAcc w b).net.count = 0 ∧ (powerModulus w b).net.count = 0 ∧
      (powerBase w b).net.count = 0 := ⟨rfl,rfl,rfl⟩
  simp only [h₀.1, h₀.2.1, h₀.2.2, zero_add, add_zero] at h₁ h₂
  simp only [powerNew, wordMux_count, powerBit, count_bit, zero_add]
  omega

lemma powerStep_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerStep w i).net.count ≤ 3672*w*w+436*w+36 := by
  have h := powerNew_count w i
  simp only [powerStep, count_pair, count_select, zero_add]
  nlinarith

lemma powerStep_pack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b) :
    (powerStep w i).eval (powerPack a m e z) =
      powerPack a m e ((powerNew w i).eval (powerPack a m e z)) := by
  simp only [powerStep, eval_pair, eval_select, powerPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma powerNew_value {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) (i : Fin b)
    (hm : 0 < (bitsValue m).toNat) :
    (bitsValue ((powerNew w i).eval (powerPack a m e z))).toNat =
      (if e i then ((bitsValue z).toNat^2 % (bitsValue m).toNat)*
        (bitsValue a).toNat % (bitsValue m).toNat
      else (bitsValue z).toNat^2 % (bitsValue m).toNat) := by
  rw [powerNew, wordMux_eval, powerBit_eval]
  have hm' : 0 < (bitsValue ((powerModulus w b).eval (powerPack a m e z))).toNat := by
    simpa only [powerModulus_eval] using hm
  split <;> rw [mulMod_word _ _ _ _ hm']
  · rw [mulMod_word _ _ _ _ hm']
    simp only [powerAcc_eval, powerBase_eval, powerModulus_eval, pow_two]
  · simp only [powerAcc_eval, powerModulus_eval, pow_two]

/-- Horner value processes the actual physical data bits from low wire to high
wire, matching the reversed input convention of the triangular transform. -/
def horner {b : ℕ} (e : Basis b) : (k : ℕ) → k ≤ b → ℕ
  | 0, _ => 0
  | k+1, h => 2*horner e k (by omega) + (e ⟨k,by omega⟩).toNat

def powerPrefix (w b : ℕ) : (k : ℕ) → k ≤ b → BooleanNetwork (powerWidth w b) (powerWidth w b)
  | 0, _ => select id
  | k+1, h => (powerPrefix w b k (by omega)).comp (powerStep w ⟨k,by omega⟩)

lemma powerPrefix_count (w b k : ℕ) (hk : k ≤ b) :
    (powerPrefix w b k hk).net.count ≤ k*(3672*w*w+436*w+36) := by
  induction k with
  | zero => simp [powerPrefix]
  | succ k ih =>
    have h := powerStep_count w (⟨k,by omega⟩ : Fin b)
    simp only [powerPrefix, count_comp]
    have hh := ih (by omega)
    nlinarith

lemma horner_pow_step (a m v : ℕ) (b : Bool) :
    (if b then ((a^v % m)^2 % m)*a % m else (a^v % m)^2 % m) =
      a^(2*v+b.toNat) % m := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
    rw [← Nat.pow_mod, ← pow_mul]
    congr 2
    omega
  · simp only [↓reduceIte, Bool.toNat_true]
    rw [← Nat.pow_mod, Nat.mod_mul_mod, ← pow_mul, pow_succ, Nat.mul_comm v 2]

lemma powerPrefix_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis w,
      (powerPrefix w b k hk).eval
        (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val)) = powerPack a m e z ∧
      (bitsValue z).toNat = (bitsValue a).toNat ^ horner e k hk % (bitsValue m).toNat := by
  induction k with
  | zero =>
    refine ⟨(fun i => (BitVec.ofNat w 1).getLsbD i.val),?_,?_⟩
    · simp only [powerPrefix, eval_select, Function.comp_id]
    · rw [bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · simp [horner, Nat.mod_eq_of_lt (by omega : 1 < (bitsValue m).toNat)]
      · have h := (bitsValue m).isLt
        omega
  | succ k ih =>
    obtain ⟨z,hz,hv⟩ := ih (by omega)
    refine ⟨(powerNew w ⟨k,by omega⟩).eval (powerPack a m e z),?_,?_⟩
    · rw [powerPrefix,eval_comp,hz,powerStep_pack]
    · rw [powerNew_value _ _ _ _ _ (by omega), hv, horner_pow_step]
      rfl

/-- The complete bounded binary-power network. Inputs remain available for
copying; the result is a separate output word. -/
def modularPower (w b : ℕ) : BooleanNetwork ((w+w)+b) w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    ((powerPrefix w b b le_rfl).rewire (Fin.natAdd ((w+w)+b)))

lemma modularPower_count (w b : ℕ) :
    (modularPower w b).net.count ≤ w+b*(3672*w*w+436*w+36) := by
  have h := powerPrefix_count w b b le_rfl
  simp only [modularPower,count_comp,count_pair,count_select,wordConstant_count,
    count_rewire,zero_add]
  omega

lemma modularPower_value {w b : ℕ} (a m : Basis w) (e : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((modularPower w b).eval (Fin.append (Fin.append a m) e))).toNat =
      (bitsValue a).toNat ^ horner e b le_rfl % (bitsValue m).toNat := by
  obtain ⟨z,hz,hv⟩ := powerPrefix_value a m e hm b le_rfl
  have hc : (wordConstant (n := (w+w)+b) (BitVec.ofNat w 1)).eval
      (Fin.append (Fin.append a m) e) =
        (fun i => (BitVec.ofNat w 1).getLsbD i.val) := by
    funext i
    simp [wordConstant]
  simp only [modularPower,eval_comp,eval_rewire,eval_pair,eval_select,
    Function.comp_id,hc]
  change (bitsValue (((powerPrefix w b b le_rfl).eval
    (powerPack a m e (fun i => (BitVec.ofNat w 1).getLsbD i.val))) ∘
      Fin.natAdd ((w+w)+b))).toNat = _
  rw [hz]
  have he : powerPack a m e z ∘ Fin.natAdd ((w+w)+b) = z := by
    funext i
    exact Fin.append_right _ _ i
  rw [he,hv]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
