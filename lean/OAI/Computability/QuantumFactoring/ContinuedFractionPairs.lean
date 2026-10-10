import Mathlib
import OAI.Computability.QuantumFactoring.ContinuedFractionRecovery

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

/-- Reduced nonnegative numerator/positive denominator representation; the zero
case is essential because the total rational inverse sends zero to zero. -/
def convergentPair (a b : ℕ) : ℕ → ℕ×ℕ
  | 0 => (a/b,1)
  | k+1 =>
    let p := convergentPair b (a%b) k
    if p.1=0 then (a/b,1) else ((a/b)*p.1+p.2,p.1)

lemma convergentPair_reduced (a b k : ℕ) :
    0<(convergentPair a b k).2 ∧
      Nat.Coprime (convergentPair a b k).1 (convergentPair a b k).2 := by
  induction k generalizing a b with
  | zero => simp [convergentPair]
  | succ k ih =>
    have hh := ih b (a%b)
    simp only [convergentPair]
    split_ifs with h
    · simp
    · constructor
      · exact Nat.pos_of_ne_zero h
      · simpa [Nat.coprime_add_mul_left_left] using hh.2.symm

lemma convergentPair_ratio (a b k : ℕ) :
    ((convergentPair a b k).1:ℚ)/(convergentPair a b k).2=euclidConvergent a b k := by
  induction k generalizing a b with
  | zero => simp [convergentPair,euclidConvergent]
  | succ k ih =>
    have hh := ih b (a%b)
    by_cases h : (convergentPair b (a%b) k).1=0
    · have he : euclidConvergent b (a%b) k=0 := by rw [← hh,h]; simp
      simp [convergentPair,h,euclidConvergent,he]
    · have hp : ((convergentPair b (a%b) k).1:ℚ) ≠ 0 := by exact_mod_cast h
      simp only [convergentPair,ite_eq_right h,Nat.cast_add,Nat.cast_mul,euclidConvergent]
      rw [← hh,inv_div,add_div,mul_div_cancel_right₀ _ hp]

lemma convergentPair_label (a b k : ℕ) :
    rationalLabel (euclidConvergent a b k)=
      ((convergentPair a b k).2,(convergentPair a b k).1) := by
  rw [← convergentPair_ratio]
  exact rationalLabel_reduced (convergentPair_reduced a b k).1 (convergentPair_reduced a b k).2

/-- Linear bit growth, rather than syntactic nested rational inverses. -/
lemma convergentPair_bound {s a b : ℕ} (ha : a<2^s) (hb : b<2^s) (k : ℕ) :
    (convergentPair a b k).1<2^(s*(k+1)+1) ∧
      (convergentPair a b k).2<2^(s*(k+1)+1) := by
  induction k generalizing a b with
  | zero =>
    have hp : 2^s ≤ 2^(s*1+1) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hone : 1<2^(s*1+1) := Nat.one_lt_two_pow (by omega)
    exact ⟨(Nat.div_le_self a b).trans_lt (ha.trans_le hp),hone⟩
  | succ k ih =>
    have hm : a%b<2^s := (Nat.mod_le a b).trans_lt ha
    obtain ⟨hn,hd⟩ := ih hb hm
    have hdiv : a/b<2^s := (Nat.div_le_self a b).trans_lt ha
    have hpow : 2^(s*(k+1)+1) ≤ 2^(s*(k+1+1)+1) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    have ha' : a/b<2^(s*(k+1+1)+1) := hdiv.trans_le
      (Nat.pow_le_pow_right (by omega) (by nlinarith))
    have hone : 1<2^(s*(k+1+1)+1) := Nat.one_lt_two_pow (by omega)
    simp only [convergentPair]
    split_ifs
    · exact ⟨ha',hone⟩
    · refine ⟨?_,hn.trans_le hpow⟩
      have hs : a/b+1 ≤ 2^s := hdiv
      have h₁ : (a/b)*(convergentPair b (a%b) k).1+(convergentPair b (a%b) k).2 <
          (a/b+1)*2^(s*(k+1)+1) := by
        have hx := Nat.mul_le_mul_left (a/b) hn.le
        nlinarith
      have h₂ := Nat.mul_le_mul_right (2^(s*(k+1)+1)) hs
      apply h₁.trans_le
      apply h₂.trans_eq
      rw [← pow_add]
      congr 1
      ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
