import OAI.NumberTheory.TotientAsymptotic.AllShiftedPrimePairs
import OAI.NumberTheory.TotientAsymptotic.SieveCutoff

namespace OAI

/-! A uniform elementary upper-bound sieve for q and bq+1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma allShiftedPrimePairs_large_bound {b X : ℕ} (hb : 0<b)
    (hX : 512*Real.log 4 ≤ Real.log X) :
    ((allShiftedPrimePairs b X).card:ℝ) ≤
      (8*(256*Real.log 4)^2+96)*X*((b:ℝ)/b.totient)/(Real.log X)^2 := by
  let L := Real.log (X:ℝ)
  let d := 256*Real.log (4:ℝ)
  let R : ℝ := (b:ℝ)/b.totient
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hd : 0<d := by dsimp [d]; positivity
  have hL : 0<L := by dsimp [L]; nlinarith
  have hX0 : (0:ℝ)<X := zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hL)
  have hR : 1≤R := totient_ratio_one_le hb
  have hz := shiftedPrimeCutoff_bounds hX
  have hy : 1<Real.exp (L/4) := Real.one_lt_exp_iff.mpr (by positivity)
  have hp := shiftedPrimePairs_log_bound hb X (shiftedPrimeCutoff L)
    (Real.exp (L/4)) hy hz.1 (shiftedPrimeCutoff_scale hX)
  have hcard : ((allShiftedPrimePairs b X).card:ℝ) ≤
      (shiftedPrimePairs b X (shiftedPrimeCutoff L)).card+shiftedPrimeCutoff L := by
    exact_mod_cast allShiftedPrimePairs_cutoff hb X (shiftedPrimeCutoff L)
  have hmain : 8*X*R/(Real.log (shiftedPrimeCutoff L))^2 ≤ 8*d^2*X*R/L^2 := by
    calc
      _ ≤ 8*X*R/(L/d)^2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (by positivity)) (pow_le_pow_left₀ (by positivity) hz.2.1 2)
      _ = _ := by field_simp
  have herr := shiftedPrimeCutoff_error hX
  rw [Real.exp_log hX0] at herr
  have herr' : 96*(X:ℝ)/L^2 ≤ 96*X*R/L^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  calc
    ((allShiftedPrimePairs b X).card:ℝ) ≤
        8*X*R/(Real.log (shiftedPrimeCutoff L))^2+
          (shiftedPrimeCutoff L+2*(Real.exp (L/4))^3) := by linarith
    _ ≤ 8*d^2*X*R/L^2+96*X*R/L^2 := add_le_add hmain (herr.trans herr')
    _ = _ := by dsimp [L,d,R]; ring

/-- Uniform in the positive coefficient b; no analytic input is assumed. -/
theorem uniform_prime_pair_bound : ∃ C : ℝ, 0<C ∧ ∀ b : ℕ, 0<b →
    ∀ X : ℕ, 2≤X → ((allShiftedPrimePairs b X).card:ℝ) ≤
      C*X*((b:ℝ)/b.totient)/(Real.log X)^2 := by
  let K := 512*Real.log (4:ℝ)
  let A := 8*(256*Real.log (4:ℝ))^2+96
  have hA : 0<A := by dsimp [A]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨A+K^2,by positivity,?_⟩
  intro b hb X hX
  have hL : 0<Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hR : 1≤(b:ℝ)/b.totient := totient_ratio_one_le hb
  by_cases hlarge : K≤Real.log X
  · apply (allShiftedPrimePairs_large_bound hb hlarge).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hpos : 0≤(X:ℝ)*((b:ℝ)/b.totient) := by positivity
    nlinarith [mul_nonneg (sq_nonneg K) hpos]
  · have hcard : ((allShiftedPrimePairs b X).card:ℝ)≤X := by
      exact_mod_cast allShiftedPrimePairs_card_le b X
    apply hcard.trans
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hsq : (Real.log X)^2≤K^2 := pow_le_pow_left₀ hL.le (le_of_not_ge hlarge) 2
    have h1 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg X : (0:ℝ)≤X)
    have h2 := mul_le_mul_of_nonneg_left hR (show 0≤(A+K^2)*X by positivity)
    nlinarith [mul_nonneg hA.le (Nat.cast_nonneg X : (0:ℝ)≤X)]

end TotientAsymptotic

end

end OAI
