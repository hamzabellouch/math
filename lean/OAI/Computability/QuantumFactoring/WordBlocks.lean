import Mathlib
import OAI.Computability.QuantumFactoring.WordNetworks

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

/-- Consecutive fixed-width words; construction duplicates a word network at
most w times and so has a direct polynomial-size bound. -/
def wordBlocks {n s w : ℕ} (f : Fin s → BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  vector (fun k => (f (finProdFinEquiv.symm k).1).rewire
    (fun _ => (finProdFinEquiv.symm k).2))

def block {s w : ℕ} (x : Basis (s*w)) (i : Fin s) : Basis w :=
  fun j => x (finProdFinEquiv (i,j))

def blockNet (s w : ℕ) (i : Fin s) : BooleanNetwork (s*w) w :=
  select (fun j => finProdFinEquiv (i,j))

@[simp] lemma blockNet_eval {s w : ℕ} (i : Fin s) (x : Basis (s*w)) :
    (blockNet s w i).eval x = block x i := rfl
@[simp] lemma blockNet_count {s w : ℕ} (i : Fin s) : (blockNet s w i).net.count=0 := rfl

lemma wordBlocks_eval {n s w : ℕ} (f : Fin s → BooleanNetwork n w) (x : Basis n) (i : Fin s) :
    block ((wordBlocks f).eval x) i=(f i).eval x := by
  funext j
  simp only [block,wordBlocks,eval_vector,eval_rewire,Function.comp_apply,Equiv.symm_apply_apply]

lemma wordBlocks_count {n s w c : ℕ} (f : Fin s → BooleanNetwork n w)
    (h : ∀ i, (f i).net.count ≤ c) : (wordBlocks f).net.count ≤ s*w*c := by
  apply count_vector_le
  intro i
  simpa only [count_rewire] using h (finProdFinEquiv.symm i).1

/-- One extra carry bit before reduction avoids overflow even on noncanonical
coefficient representatives; all arrays use exactly as many bits as specified. -/
def addMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w 1)).pair (b.comp (padRight w 1))).comp (add (w+1))
  ((p.pair (m.comp (padRight w 1))).comp (mod (w+1))).rewire (Fin.castAdd 1)

lemma addMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (addMod a b m).net.count ≤ a.net.count+b.net.count+m.net.count+
      216*(w+1)^2+142*(w+1)+15 := by
  have h₁ := add_count (w+1)
  have h₂ := mod_count (w+1)
  simp only [addMod,count_rewire,count_comp,count_pair,count_padRight]
  nlinarith

lemma addMod_value {n w : ℕ} (a b m : BooleanNetwork n w) (x : Basis n)
    (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((addMod a b m).eval x)).toNat =
      ((bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat := by
  simp only [addMod,eval_rewire,eval_comp,eval_pair]
  rw [bitsValue_take,mod_word,BitVec.toNat_setWidth,BitVec.toNat_umod,add_word,BitVec.toNat_add]
  simp only [padRight_word,setWidth_toNat_of_le (by omega : w ≤ w+1)]
  have hp : (bitsValue (a.eval x)).toNat+(bitsValue (b.eval x)).toNat < 2^(w+1) := by
    rw [pow_succ]
    have ha := (bitsValue (a.eval x)).isLt
    have hb := (bitsValue (b.eval x)).isLt
    omega
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ hm).trans (bitsValue (m.eval x)).isLt

/-- Linear-length modular accumulation, not a repeated expanded expression. -/
def sumMod {n w : ℕ} (m : BooleanNetwork n w) : List (BooleanNetwork n w) → BooleanNetwork n w
  | [] => wordConstant 0
  | a::as => addMod a (sumMod m as) m

lemma sumMod_value {n w : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    (bitsValue ((sumMod m as).eval x)).toNat =
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).sum%(bitsValue (m.eval x)).toNat := by
  induction as with
  | nil => simp [sumMod,wordConstant_eval]
  | cons a as ih =>
    rw [sumMod,addMod_value _ _ _ _ hm,ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_mod_mod]

lemma sumMod_count {n w c : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (h : ∀ a ∈ as, a.net.count ≤ c) :
    (sumMod m as).net.count ≤ w+as.length*(c+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  induction as with
  | nil => simp [sumMod,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb]))
    have hh := addMod_count a (sumMod m as) m
    simp only [sumMod,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
