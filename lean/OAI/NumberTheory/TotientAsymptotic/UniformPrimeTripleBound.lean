import OAI.NumberTheory.TotientAsymptotic.AllPrimeTriples
import OAI.NumberTheory.TotientAsymptotic.TripleSieveCutoff
import OAI.NumberTheory.TotientAsymptotic.AllShiftedPrimePairs

namespace OAI

/-! A uniform upper-bound sieve for the three prime linear forms. -/
noncomputable section
namespace TotientAsymptotic

lemma allPrimeTriples_large_bound {a b X : ℕ} (ha : 0 < a) (hab : a < b)
    (hX : 512*Real.log 4 ≤ Real.log X) :
    ((allPrimeTriples a b X).card:ℝ) ≤
      (54*(256*Real.log 4)^3+1152)*X*
        ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3 := by
  let L := Real.log (X:ℝ)
  let d := 256*Real.log (4:ℝ)
  let R : ℝ := ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  have hL : 0 < L := by dsimp [L]; nlinarith
  have hX0 : (0:ℝ) < X := zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL)
  have hR : 1 ≤ R := by
    have hh := totient_ratio_one_le (tripleDiscriminant_pos ha hab)
    dsimp [R]
    nlinarith
  have hz := shiftedPrimeCutoff_bounds hX
  have hy : 1 < Real.exp (L/4) := Real.one_lt_exp_iff.mpr (by positivity)
  have hp := triplePrimeTuples_log_bound ha hab X (shiftedPrimeCutoff L)
    (Real.exp (L/4)) hy (tripleSieveCutoff_three hX) (tripleSieveCutoff_scale hX)
  have hcard : ((allPrimeTriples a b X).card:ℝ) ≤
      (triplePrimeTuples a b X (shiftedPrimeCutoff L)).card+shiftedPrimeCutoff L := by
    exact_mod_cast allPrimeTriples_cutoff ha (ha.trans hab) X (shiftedPrimeCutoff L)
  have hmain : 54*X*R/(Real.log (shiftedPrimeCutoff L))^3 ≤ 54*d^3*X*R/L^3 := by
    calc
      _ ≤ 54*X*R/(L/d)^3 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos (by positivity) 3) (pow_le_pow_left₀ (by positivity) hz.2.1 3)
      _ = _ := by field_simp
  have herr := tripleSieveCutoff_error hX
  rw [Real.exp_log hX0] at herr
  have herr' : 1152*(X:ℝ)/L^3 ≤ 1152*X*R/L^3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  calc
    _ ≤ 54*X*R/(Real.log (shiftedPrimeCutoff L))^3+
        (shiftedPrimeCutoff L+2*(Real.exp (L/4))^3) := by linarith
    _ ≤ 54*d^3*X*R/L^3+1152*X*R/L^3 := add_le_add hmain (herr.trans herr')
    _ = _ := by dsimp [L,d,R]; ring

 theorem uniform_prime_triple_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ,
    0 < a → a < b → ∀ X : ℕ, 2 ≤ X →
    ((allPrimeTriples a b X).card:ℝ) ≤ C*X*
      ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3 := by
  let K := 512*Real.log (4:ℝ)
  let A := 54*(256*Real.log (4:ℝ))^3+1152
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A+K^3,by positivity,?_⟩
  intro a b ha hab X hX
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hR : 1 ≤ ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by
    have hh := totient_ratio_one_le (tripleDiscriminant_pos ha hab)
    nlinarith
  by_cases hlarge : K ≤ Real.log X
  · apply (allPrimeTriples_large_bound ha hab hlarge).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hpos : 0 ≤ (X:ℝ)*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by positivity
    nlinarith [mul_nonneg (pow_nonneg hK.le 3) hpos]
  · have hcard : ((allPrimeTriples a b X).card:ℝ) ≤ X := by exact_mod_cast allPrimeTriples_card_le a b X
    apply hcard.trans
    apply (le_div_iff₀ (pow_pos hL 3)).mpr
    have hpow := pow_le_pow_left₀ hL.le (le_of_not_ge hlarge) 3
    have h1 := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg X : (0:ℝ) ≤ X)
    have h2 := mul_le_mul_of_nonneg_left hR (show 0 ≤ (A+K^3)*X by positivity)
    nlinarith [mul_nonneg hA.le (Nat.cast_nonneg X : (0:ℝ) ≤ X)]

end TotientAsymptotic

end

end OAI
