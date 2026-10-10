import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales

namespace OAI

noncomputable section
namespace Ostmann.ZeroDensity

def supplyConductorCutoff (L : ℝ) : ℕ :=
  ⌈Real.exp (2*(Ostmann.Supply.supplyTruncation L : ℝ)*Real.exp (9*L/10))⌉₊

def supplyPrimeSample (L : ℝ) : ℕ := (Ostmann.Supply.supplyRadius L)^2

theorem supplyConductorCutoff_pos (L : ℝ) : 0 < supplyConductorCutoff L :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem supplyPrimeSample_pos (L : ℝ) : 0 < supplyPrimeSample L := by
  exact pow_pos (Ostmann.Supply.supplyRadius_pos L) _

theorem log_supplyConductorCutoff_bound {L : ℝ} (hL : 1 ≤ L) :
    Real.log (supplyConductorCutoff L : ℝ) ≤ 20003*L*Real.exp (9*L/10) := by
  let A : ℝ := 2*(Ostmann.Supply.supplyTruncation L : ℝ)*Real.exp (9*L/10)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heA : 1 ≤ Real.exp A := Real.one_le_exp hA
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos A).le
  have hcut : (supplyConductorCutoff L : ℝ) ≤ 2*Real.exp A := by
    change (⌈Real.exp A⌉₊ : ℝ) ≤ _
    linarith
  have hp : (0 : ℝ) < supplyConductorCutoff L := Nat.cast_pos.mpr (supplyConductorCutoff_pos L)
  have hlog := Real.log_le_log hp hcut
  rw [Real.log_mul (by norm_num) (Real.exp_pos A).ne', Real.log_exp] at hlog
  have hkceil := Nat.ceil_lt_add_one (show 0 ≤ 10000*L by positivity)
  have hk : (Ostmann.Supply.supplyTruncation L : ℝ) ≤ 10001*L := by
    unfold Ostmann.Supply.supplyTruncation
    linarith
  have he : 1 ≤ Real.exp (9*L/10) := Real.one_le_exp (by positivity)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  dsimp [A] at hlog
  nlinarith [mul_le_mul_of_nonneg_right hk (Real.exp_pos (9*L/10)).le]

theorem log_supplyPrimeSample_lower (L : ℝ) :
    Real.exp L ≤ Real.log (supplyPrimeSample L : ℝ) := by
  have hlower := Nat.le_ceil (Real.exp (Real.exp L/2))
  have hlog := Real.log_le_log (Real.exp_pos (Real.exp L/2)) hlower
  rw [Real.log_exp] at hlog
  unfold supplyPrimeSample
  push_cast
  rw [Real.log_pow]
  change Real.exp L ≤ 2*Real.log (Ostmann.Supply.supplyRadius L : ℝ)
  change Real.exp L/2 ≤ Real.log (Ostmann.Supply.supplyRadius L : ℝ) at hlog
  linarith

theorem log_supplyPrimeSample_upper (L : ℝ) :
    Real.log (supplyPrimeSample L : ℝ) ≤ Real.exp L+2*Real.log 2 := by
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (Real.exp L/2)).le
  have hexp : 1 ≤ Real.exp (Real.exp L/2) := Real.one_le_exp (by positivity)
  have hrad : (Ostmann.Supply.supplyRadius L : ℝ) ≤ 2*Real.exp (Real.exp L/2) := by
    unfold Ostmann.Supply.supplyRadius
    linarith
  have hp : (0 : ℝ)<Ostmann.Supply.supplyRadius L :=
    Nat.cast_pos.mpr (Ostmann.Supply.supplyRadius_pos L)
  have hlog := Real.log_le_log hp hrad
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog
  unfold supplyPrimeSample
  push_cast
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem log_supplyPrimeSample_bounds {L : ℝ} (hL : 1 ≤ L) :
    Real.exp L ≤ Real.log (supplyPrimeSample L : ℝ) ∧
      Real.log (supplyPrimeSample L : ℝ) ≤ 2*Real.exp L := by
  refine ⟨log_supplyPrimeSample_lower L,?_⟩
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have he := Real.add_one_le_exp L
  have hu := log_supplyPrimeSample_upper L
  linarith

end Ostmann.ZeroDensity

end

end OAI
