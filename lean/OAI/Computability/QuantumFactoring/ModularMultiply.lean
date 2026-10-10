import Mathlib
import OAI.Computability.QuantumFactoring.WordNetworks

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Full double-width product followed by full double-width remainder, with no
word overflow. The narrow remainder is valid because the modulus is a word. -/
def mulMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w w)).pair (b.comp (padRight w w))).comp (mul (w+w))
  ((p.pair (m.comp (padRight w w))).comp (mod (w+w))).rewire (Fin.castAdd w)

lemma mulMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (mulMod a b m).net.count ≤
      a.net.count + b.net.count + m.net.count + (1224*w*w+143*w+12) := by
  have h₁ := mul_count (w+w)
  have h₂ := mod_count (w+w)
  simp only [mulMod, count_rewire, count_comp, count_pair, count_padRight]
  nlinarith

lemma mulMod_word {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((mulMod a b m).eval x)).toNat =
      (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat %
        (bitsValue (m.eval x)).toNat := by
  simp only [mulMod, eval_rewire, eval_comp, eval_pair]
  rw [bitsValue_take, mod_word, BitVec.toNat_setWidth, BitVec.toNat_umod,
    mul_word, BitVec.toNat_mul]
  simp only [padRight_word, setWidth_toNat_of_le (by omega : w ≤ w+w)]
  have hp : (bitsValue (a.eval x)).toNat * (bitsValue (b.eval x)).toNat < 2^(w+w) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (bitsValue (a.eval x)).isLt
      (bitsValue (b.eval x)).isLt
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

/-- A word mux shares previously computed word outputs via fanout; it does not
recompute the operand circuit separately at every bit. -/
def wordMux {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    BooleanNetwork n w :=
  ((c.pair a).pair b).comp (vector (fun i =>
    mux (bit ⟨0,by omega⟩) (bit ⟨1+i.val,by omega⟩)
      (bit ⟨1+w+i.val,by omega⟩)))

lemma wordMux_eval {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w)
    (x : Basis n) :
    (wordMux c a b).eval x = if c.eval x 0 then a.eval x else b.eval x := by
  funext i
  simp only [wordMux, eval_comp, eval_vector, eval_mux, eval_bit, eval_pair]
  have h₀ : (⟨0,by omega⟩ : Fin (1+w+w)) = (Fin.castAdd w ((0 : Fin 1).castAdd w)) := rfl
  have h₁ : (⟨1+i.val,by omega⟩ : Fin (1+w+w)) = (Fin.natAdd 1 i).castAdd w := rfl
  have h₂ : (⟨1+w+i.val,by omega⟩ : Fin (1+w+w)) = Fin.natAdd (1+w) i := rfl
  simp only [h₀,h₁,h₂,Fin.append_left,Fin.append_right]
  split <;> rfl

lemma wordMux_count {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    (wordMux c a b).net.count = c.net.count+a.net.count+b.net.count+7*w := by
  simp [wordMux, count_comp, count_pair, Nat.mul_comm]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
