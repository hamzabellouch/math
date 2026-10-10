import Mathlib
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.StaticPredicates

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma all_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (all (List.ofFn cs)).eval x 0=true ↔ ∀ i, (cs i).eval x 0=true := by
  rw [all_eval]
  simp

lemma any_ofFn_eval {n k : ℕ} (cs : Fin k → BooleanNetwork n 1) (x : Basis n) :
    (any (List.ofFn cs)).eval x 0=true ↔ ∃ i, (cs i).eval x 0=true := by
  rw [any_eval]
  simp

lemma bnot_value {n : ℕ} (c : BooleanNetwork n 1) (x : Basis n) :
    c.bnot.eval x 0=true ↔ ¬ c.eval x 0=true := by simp

end ExactQuantumFactoring.BooleanNetwork

namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def orderTests (w s k : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot))

lemma orderTests_value (w s k : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hkw : k < 2^w) :
    (orderTests w s k).eval x 0=true ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → (bitsValue x).toNat^j%s ≠ 1 := by
  rw [orderTests,all_ofFn_eval]
  constructor
  · intro h j hj hjk
    have hh := (bnot_value _ _).mp (h (⟨j-1,by omega⟩ : Fin k))
    rw [powerOneNet_value _ _ _ _ hs hsw (by omega)] at hh
    simpa only [show j-1+1=j by omega] using hh
  · intro h i
    rw [bnot_value,powerOneNet_value _ _ _ _ hs hsw (by have := i.isLt;omega)]
    exact h (i.val+1) (by omega) (by omega)

lemma orderTests_count (w s k : ℕ) : (orderTests w s k).net.count ≤
    k*(100*w+23+w*(3672*w*w+436*w+36))+1 := by
  have h := all_count (c := 100*w+22+w*(3672*w*w+436*w+36))
    (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := powerOneNet_count w s (i.val+1)
      omega)
  convert h using 1 <;> simp only [orderTests,List.length_ofFn]
  ring

def properDivisor (w d : ℕ) : BooleanNetwork w 1 :=
  (dividesNet w d).band (wordLt (wordConstant (BitVec.ofNat w d)) (select id))

lemma properDivisor_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (properDivisor w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat ∧ d < (bitsValue x).toNat := by
  rw [properDivisor,eval_band,Bool.and_eq_true,dividesNet_value _ _ _ hd,
    wordLt_eval,wordConstant_eval,eval_select,Function.comp_id,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hd,decide_eq_true_eq]

lemma properDivisor_count (w d : ℕ) :
    (properDivisor w d).net.count ≤ 216*w*w+203*w+36 := by
  have h := wordLt_count (wordConstant (n := w) (BitVec.ofNat w d)) (select id)
  rw [wordConstant_count,count_select] at h
  have hd := dividesNet_count w d
  rw [properDivisor,count_band]
  omega

def noSmallDivisor (w B : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot))

lemma noSmallDivisor_value (w B : ℕ) (x : Basis w) (hB : B < 2^w) :
    (noSmallDivisor w B).eval x 0=true ↔
      ∀ d : ℕ, 2 ≤ d → d ≤ B → d < (bitsValue x).toNat → ¬ d ∣ (bitsValue x).toNat := by
  rw [noSmallDivisor,all_ofFn_eval]
  constructor
  · intro h d hd hdB hdm hdiv
    have hh := (bnot_value _ _).mp (h (⟨d-2,by omega⟩ : Fin (B-1)))
    rw [properDivisor_value _ _ _ (by omega)] at hh
    exact hh (by simpa [show d-2+2=d by omega] using And.intro hdiv hdm)
  · intro h i
    rw [bnot_value,properDivisor_value _ _ _ (by have := i.isLt;omega)]
    rintro ⟨hd,hlt⟩
    exact h (i.val+2) (by omega) (by omega) hlt hd

lemma noSmallDivisor_count (w B : ℕ) : (noSmallDivisor w B).net.count ≤
    (B-1)*(216*w*w+203*w+38)+1 := by
  have h := all_count (c := 216*w*w+203*w+37)
    (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := properDivisor_count w (i.val+2)
      omega)
  simpa only [noSmallDivisor,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
