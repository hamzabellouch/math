import OAI.NumberTheory.TotientAsymptotic.InitialRoughEncoding

namespace OAI

/-! Exact sieve data supplied by extraction from the initial rough factor. -/
noncomputable section
namespace TotientAsymptotic

structure InitialPrimeData (a b d : ℕ) (y L : ℝ) (e : ℕ × ℕ) : Prop where
  residual_pos : 0 < e.1
  prime : e.2.Prime
  log_lower : L ≤ Real.log e.2
  size : ((d*e.1*e.2:ℕ):ℝ) ≤ y
  left_pos : 0 < a*e.1
  right_pos : 0 < b*e.1
  left_le : ((a*e.1:ℕ):ℝ) ≤ y
  right_le : ((b*e.1:ℕ):ℝ) ≤ y
  different : a*e.1 ≠ b*e.1
  left_prime : (a*e.1*e.2+1).Prime
  right_prime : (b*e.1*e.2+1).Prime

lemma initial_rough_sieve_data {a b d : ℕ} {y U : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hy : Real.exp 2 ≤ y) (hBy : 1 ≤ B y)
    (hn : InitialRoughConditions a b d y U n) :
    InitialPrimeData a b d y (Real.log y/(6*B y)) (initialRoughEncoding n) := by
  have hres := initial_rough_residual hy hn
  have he := initial_rough_product hy hn
  have hvle : (initialRoughEncoding n).1 ≤ n := Nat.div_le_self _ _
  have hvl : ((a*(initialRoughEncoding n).1:ℕ):ℝ) ≤ ((a*n:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left a hvle
  have hvr : ((b*(initialRoughEncoding n).1:ℕ):ℝ) ≤ ((b*n:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left b hvle
  have hleft : a*(initialRoughEncoding n).1*(initialRoughEncoding n).2+1=a*n+1 := by
    rw [mul_assoc,he]
  have hright : b*(initialRoughEncoding n).1*(initialRoughEncoding n).2+1=b*n+1 := by
    rw [mul_assoc,he]
  refine ⟨hres.1,hres.2.1,initial_rough_log_largest hy hBy hn,?_,
    Nat.mul_pos ha hres.1,Nat.mul_pos hb hres.1,hvl.trans hn.left_le,hvr.trans hn.right_le,?_,?_,?_⟩
  · rw [mul_assoc,he]
    exact hn.size
  · intro hh
    apply hn.different
    rw [← hleft,← hright,hh]
  · rw [hleft]
    exact hn.left_prime
  · rw [hright]
    exact hn.right_prime

end TotientAsymptotic

end

end OAI
