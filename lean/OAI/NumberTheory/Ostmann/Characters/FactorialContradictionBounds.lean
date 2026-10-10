import Mathlib.Analysis.SpecialFunctions.Stirling
import OAI.NumberTheory.Ostmann.Characters.ParityPermutations

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Characters

def factorialCount (n m : ℕ) : ℕ := ((Nat.factorial (2^n))^2)^m

def factorialMass (n m : ℕ) : ℝ := (2 : ℝ)^(n+1) * m

theorem factorialCount_eq_card (n m : ℕ) :
    factorialCount n m = Fintype.card (ParityReassignments n m) :=
  (card_parityReassignments n m).symm

theorem factorialCount_pos (n m : ℕ) : 0 < factorialCount n m := by
  unfold factorialCount
  positivity

theorem factorialMass_nonneg (n m : ℕ) : 0 ≤ factorialMass n m := by
  unfold factorialMass
  positivity

theorem log_factorial_lower {a : ℕ} (ha : a ≠ 0) :
    (a : ℝ) * Real.log a - a ≤ Real.log (Nat.factorial a : ℝ) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
  have hlog := Real.log_nonneg ha1
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by have := Real.pi_gt_three; linarith)
  have h := Stirling.le_log_factorial_stirling ha
  linarith

theorem log_factorialCount_lower (n m : ℕ) :
    factorialMass n m * ((n : ℝ) * Real.log 2 - 1) ≤
      Real.log (factorialCount n m : ℝ) := by
  have h := log_factorial_lower (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * (m : ℝ) by positivity)
  simpa only [factorialCount, Nat.cast_pow, Real.log_pow, factorialMass,
    Nat.cast_ofNat] using (show
      (2 : ℝ)^(n+1) * (m : ℝ) * ((n : ℝ) * Real.log 2 - 1) ≤
        (m : ℝ) * (2 * Real.log (Nat.factorial (2^n) : ℝ)) by
      simp only [pow_succ]
      nlinarith [hmul])

theorem exp_le_factorialCount (n m : ℕ) :
    Real.exp (factorialMass n m * ((n : ℝ) * Real.log 2 - 1)) ≤
      (factorialCount n m : ℝ) := by
  have hpos : (0 : ℝ) < factorialCount n m := by exact_mod_cast factorialCount_pos n m
  exact (Real.exp_le_exp.mpr (log_factorialCount_lower n m)).trans_eq (Real.exp_log hpos)

theorem exists_factorial_depth (B BD C ε : ℝ) (hε : 60 * ε < Real.log 2)
    (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧
      BD + 60 * ε * (n+1) + C + 2*B + 2 ≤ (n : ℝ)*Real.log 2 - 1 := by
  have hd : 0 < Real.log 2 - 60 * ε := sub_pos.mpr hε
  obtain ⟨a, ha⟩ := exists_nat_gt ((BD + C + 2*B + 3 + 60*ε) /
    (Real.log 2 - 60*ε))
  let n := max a n₀
  have han : (a : ℝ) ≤ n := by exact_mod_cast le_max_left a n₀
  have hn := (div_lt_iff₀ hd).mp (ha.trans_le han)
  refine ⟨n, le_max_right a n₀, ?_⟩
  nlinarith

end Ostmann.Characters

end

end OAI
