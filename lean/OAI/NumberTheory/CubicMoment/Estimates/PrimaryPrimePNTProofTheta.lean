import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Prime-power removal for the mod-three von Mangoldt mean. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Filter Topology MeasureTheory
namespace CubicFirstMoment

/-- Rational primes in one residue class, with the literal real cutoff. -/
def rationalProgressionPrimes (a : ℕ) (X : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = a)

def rationalProgressionCount (a : ℕ) (X : ℝ) : ℝ :=
  (rationalProgressionPrimes a X).card

def rationalProgressionTheta (a : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ rationalProgressionPrimes a X, Real.log p

def modThreePsi (a : ZMod 3) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, vonMangoldt.residueClass a n

theorem modThreePsi_limit (a : ZMod 3) (ha : IsUnit a) :
    Tendsto (fun X => modThreePsi a X / X) atTop (𝓝 (1/2 : ℝ)) := by
  have h := (modThree_mangoldt_mean a ha).comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  have hratio : Tendsto (fun X : ℝ => (⌊X⌋₊ + 1 : ℝ) / X) atTop (𝓝 1) := by
    have hh := (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero
    simpa only [one_div, add_div, add_zero] using hh
  have hh := h.mul hratio
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hN : (⌊X⌋₊ + 1 : ℝ) ≠ 0 := by positivity
  rw [modThreePsi, cumsum, ← Nat.range_succ_eq_Icc_zero]
  field_simp

lemma rationalProgression_primePower_gap {a : ℕ} (ha : a < 3) (X : ℝ) :
    0 ≤ modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ∧
    modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ≤
      Chebyshev.psi X - Chebyshev.theta X := by
  let f := vonMangoldt.residueClass (a : ZMod 3)
  have hf (n : ℕ) : f n = if n % 3 = a then vonMangoldt n else 0 := by
    simp only [f, vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha]
  have htheta : rationalProgressionTheta a X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then f n else 0 := by
    simp only [rationalProgressionTheta, rationalProgressionPrimes, Finset.sum_filter,
      Nat.primesLE_eq_filter_Icc_zero]
    apply Finset.sum_congr rfl
    intro n _
    rw [hf]
    by_cases hn : n.Prime <;> simp [hn,vonMangoldt_apply_prime]
  have heq : modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then 0 else f n := by
    rw [htheta, modThreePsi, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime <;> simp [hn,f]
  have hall : Chebyshev.psi X - Chebyshev.theta X =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, if n.Prime then 0 else vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime <;> simp [hn,vonMangoldt_apply_prime]
  rw [heq,hall]
  constructor
  · apply Finset.sum_nonneg
    intro n _
    split_ifs <;> [rfl; exact vonMangoldt.residueClass_nonneg _ _]
  · apply Finset.sum_le_sum
    intro n _
    split_ifs <;> [rfl; exact vonMangoldt.residueClass_le _ _]

lemma sqrt_log_div_tendsto_zero :
    Tendsto (fun X : ℝ => 2 * Real.sqrt X * Real.log X / X) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero).const_mul 2
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [← Real.sqrt_eq_rpow]
  have hs := ne_of_gt (Real.sqrt_pos.mpr hX)
  calc
    2 * (Real.log X / Real.sqrt X) =
        2 * Real.sqrt X * Real.log X / (Real.sqrt X ^ 2) := by field_simp
    _ = _ := by rw [Real.sq_sqrt hX.le]

theorem rationalProgressionTheta_limit {a : ℕ} (ha : a = 1 ∨ a = 2) :
    Tendsto (fun X => rationalProgressionTheta a X / X) atTop (𝓝 (1/2 : ℝ)) := by
  have hau : IsUnit (a : ZMod 3) := by
    rcases ha with rfl | rfl
    · exact isUnit_one
    · apply isUnit_iff_ne_zero.mpr
      decide
  have ha3 : a < 3 := by omega
  have hp := modThreePsi_limit (a : ZMod 3) hau
  have hl := hp.sub sqrt_log_div_tendsto_zero
  norm_num at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hp
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hg := (rationalProgression_primePower_gap ha3 X).2
    have hh := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX
    have hb : modThreePsi (a : ZMod 3) X - rationalProgressionTheta a X ≤
        2 * Real.sqrt X * Real.log X := hg.trans ((le_abs_self _).trans hh)
    have hd := div_le_div_of_nonneg_right hb (show 0 ≤ X by linarith)
    rw [sub_div] at hd
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact sub_nonneg.mp (rationalProgression_primePower_gap ha3 X).1

end CubicFirstMoment

end

end OAI
