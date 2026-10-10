import OAI.Combinatorics.ContingencyTables.Transport.RationalRootBisection
import Mathlib.Data.Rat.Floor

namespace OAI

/-! # A bounded rational approximation to the evaluator's power of two -/

namespace ContingencyTables.PowerOfTwoApproximation

open RationalRootBisection

noncomputable section

def numerator (beta : ℚ) (s : ℕ) : ℤ := ⌊(s:ℚ)*beta⌋

def rounded (beta : ℚ) (s : ℕ) : ℝ := (numerator beta s:ℝ)/s

def approximation (beta : ℚ) (s n : ℕ) : ℚ := midpoint ((2:ℚ)^numerator beta s) s n

lemma rounded_bounds (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    rounded beta s ≤ (beta:ℝ) ∧ (beta:ℝ)-rounded beta s ≤ 1/(s:ℝ) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hlow : (numerator beta s:ℚ) ≤ (s:ℚ)*beta := Int.floor_le _
  have hhigh : (s:ℚ)*beta < (numerator beta s:ℚ)+1 := Int.lt_floor_add_one _
  have hl : (numerator beta s:ℝ) ≤ (s:ℝ)*(beta:ℝ) := by exact_mod_cast hlow
  have hu : (s:ℝ)*(beta:ℝ) < (numerator beta s:ℝ)+1 := by exact_mod_cast hhigh
  constructor
  · exact (div_le_iff₀ hsR).mpr (by simpa only [mul_comm] using hl)
  · unfold rounded
    apply (le_div_iff₀ hsR).mpr
    have he : ((beta:ℝ)-(numerator beta s:ℝ)/(s:ℝ))*(s:ℝ)=
        (s:ℝ)*(beta:ℝ)-(numerator beta s:ℝ) := by field_simp
    rw [he]
    linarith

lemma rounded_power_root (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    ((2:ℝ)^rounded beta s)^s=(((2:ℚ)^numerator beta s:ℚ):ℝ) := by
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  unfold rounded
  rw [div_mul_cancel₀ _ hsR,Real.rpow_intCast]
  exact (Rat.cast_zpow _ _).symm

/-- Rounding downward loses at most 1/s in relative value. The proof uses
only the tangent bound for exp and log 2 ≤ 1. -/
lemma rounded_power_error (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    0 ≤ (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ∧
      (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ≤ (2:ℝ)^(beta:ℝ)/(s:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hT : 0 < (2:ℝ)^(beta:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hd : rounded beta s-(beta:ℝ) ≤ 0 := by linarith [hb.1]
  have hmul := mul_le_mul_of_nonpos_right hlog hd
  have he := Real.add_one_le_exp (Real.log 2*(rounded beta s-(beta:ℝ)))
  have hlower : 1-1/(s:ℝ) ≤ (2:ℝ)^rounded beta s/(2:ℝ)^(beta:ℝ) := by
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [hb.2]
  have hprod := (le_div_iff₀ hT).mp hlower
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) hb.1)
  · calc
      _ ≤ (2:ℝ)^(beta:ℝ)-(1-1/(s:ℝ))*(2:ℝ)^(beta:ℝ) := by linarith
      _ = _ := by ring

/-- The only non-rational quantity in the proof is the target. The
returned value is the midpoint of a fixed number of rational comparisons. -/
theorem approximation_error (beta : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (s n : ℕ) (hs : 0 < s) (sigma : ℝ)
    (hbudget : 1/(s:ℝ)+32/(2:ℝ)^n ≤ sigma) :
    |(approximation beta s n:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ sigma*(2:ℝ)^(beta:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hp := rounded_power_error beta s hs
  have ht0 : 0 ≤ (2:ℝ)^rounded beta s := (Real.rpow_pos_of_pos (by norm_num) _).le
  have ht8 : (2:ℝ)^rounded beta s ≤ 8 := by
    have hr : rounded beta s ≤ 2 := hb.1.trans (by exact_mod_cast hhi)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at hh
    linarith
  have hT : (1/4:ℝ) ≤ (2:ℝ)^(beta:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (-2:ℝ) ≤ (beta:ℝ) by exact_mod_cast hlo)
    norm_num at hh
    exact hh
  have he := midpoint_error ((2:ℚ)^numerator beta s) s hs ((2:ℝ)^rounded beta s)
    ht0 ht8 (rounded_power_root beta s hs) n
  have hscale : 8/(2:ℝ)^n ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 32/(2:ℝ)^n by positivity)
    convert hh using 1; ring
  have htpos : 0 ≤ (2:ℝ)^(beta:ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ |(approximation beta s n:ℝ)-(2:ℝ)^rounded beta s|+
        |(2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ)| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        ((approximation beta s n:ℝ)-(2:ℝ)^rounded beta s)
        ((2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ))
    _ ≤ 8/(2:ℝ)^n+(2:ℝ)^(beta:ℝ)/(s:ℝ) := by
      exact add_le_add he (by rw [abs_of_nonpos (by linarith [hp.1])]; linarith [hp.2])
    _ ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ)+(2:ℝ)^(beta:ℝ)/(s:ℝ) := add_le_add hscale le_rfl
    _ = (1/(s:ℝ)+32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget htpos

def rootDegree (sigma : ℚ) : ℕ := ⌈128/sigma⌉₊

def depth (sigma : ℚ) : ℕ := Nat.clog 2 (rootDegree sigma)

def approximate (beta sigma : ℚ) : ℚ := approximation beta (rootDegree sigma) (depth sigma)

lemma degree_positive (sigma : ℚ) (hsigma : 0 < sigma) : 0 < rootDegree sigma := by
  have h := Nat.le_ceil (128/sigma:ℚ)
  have hp : (0:ℚ) < 128/sigma := by positivity
  have hc : (0:ℚ) < rootDegree sigma := lt_of_lt_of_le hp h
  exact_mod_cast hc

lemma degree_le (sigma : ℚ) (hsigma : 0 < sigma) :
    (rootDegree sigma:ℚ) ≤ 128/sigma+1 := by
  exact (Nat.ceil_lt_add_one (by positivity : (0:ℚ) ≤ 128/sigma)).le

lemma error_budget (sigma : ℚ) (hsigma : 0 < sigma) :
    1/(rootDegree sigma:ℝ)+32/(2:ℝ)^depth sigma ≤ (sigma:ℝ) := by
  have hs := degree_positive sigma hsigma
  have hsR : (0:ℝ) < rootDegree sigma := by exact_mod_cast hs
  have hsigmaR : (0:ℝ) < sigma := by exact_mod_cast hsigma
  have hceil : (128:ℝ)/(sigma:ℝ) ≤ rootDegree sigma := by
    have hh := Nat.le_ceil (128/sigma:ℚ)
    exact_mod_cast hh
  have hpow : (rootDegree sigma:ℝ) ≤ (2:ℝ)^depth sigma := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (rootDegree sigma)
  have hrec : 1/(rootDegree sigma:ℝ) ≤ (sigma:ℝ)/128 := by
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<128)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  have hrec' : 32/(2:ℝ)^depth sigma ≤ (sigma:ℝ)/4 := by
    apply (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 32) hsR hpow).trans
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<4)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  linarith

theorem approximate_error (beta sigma : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (hsigma : 0 < sigma) :
    |(approximate beta sigma:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ (sigma:ℝ)*(2:ℝ)^(beta:ℝ) :=
  approximation_error beta hlo hhi _ _ (degree_positive sigma hsigma) _ (error_budget sigma hsigma)

theorem approximate_positive (beta sigma : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) : 0 < approximate beta sigma := by
  have he := approximate_error beta sigma hlo hhi hsigma
  have hT : 0 < (2:ℝ)^(beta:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hl := (abs_le.mp he).1
  have hsigmaR : (sigma:ℝ) < 1 := by exact_mod_cast hsigma1
  have hpos : (0:ℝ) < approximate beta sigma := by nlinarith
  exact_mod_cast hpos

end

end ContingencyTables.PowerOfTwoApproximation

end OAI
