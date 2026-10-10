import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationTargets
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Every prescribed compensation target lies in the small-prime range -/

namespace Ostmann
open Filter

theorem movingCompensationTargets_mem_bounds (J B : ℝ) (ds : List ℝ)
    (hJ : 0 ≤ J) (hB : 0 ≤ B) (hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    ∀ w ∈ movingCompensationTargets J ds,
      J - 2 ^ ds.length * B ≤ w ∧ w ≤ 2 ^ ds.length * J := by
  induction ds with
  | nil => simp [movingCompensationTargets]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ B := fun e he => hd e (by simp [he])
    have herror := movingCompensationTargetError_bounds B ds hds
    have hsum := movingCompensationTargets_sum J ds
    have hp : (1 : ℝ) ≤ 2 ^ ds.length := one_le_pow₀ (by norm_num)
    have hpJ := mul_le_mul_of_nonneg_right hp hJ
    have hpB : 0 ≤ (2 : ℝ) ^ ds.length * B := by positivity
    have hpJ0 : 0 ≤ (2 : ℝ) ^ ds.length * J := by positivity
    intro w hw
    simp only [movingCompensationTargets, List.mem_cons] at hw
    simp only [List.length_cons, pow_succ]
    rcases hw with rfl | hw
    · constructor <;> nlinarith only [hsum, herror.1, herror.2, hd0.1, hd0.2, hpJ, hpB, hpJ0]
    · obtain ⟨hl, hu⟩ := ih hds w hw
      constructor <;> nlinarith only [hl, hu, hpB, hpJ0]

theorem eventual_moving_compensation_range (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : ℝ) (ds : List ℝ), ds.length ≤ k →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      (∀ d ∈ ds, 0 ≤ d ∧ d ≤ B * L) →
      ∀ w ∈ movingCompensationTargets J ds,
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  let C := (2 : ℝ) ^ k * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : Tendsto (fun L : ℝ => Real.exp ((5 / 10000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [arithmetic_exponent_absorption 0 (1 / 100) 0 C 8 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ht.eventually (eventually_ge_atTop (8 * (2 : ℝ) ^ k)),
    eventually_ge_atTop (0 : ℝ)] with L hgap hratio hL
  intro J ds hlen hJlo hJhi hd w hw
  have hJ : 0 ≤ J := (by positivity : 0 ≤ 16 * Real.exp ((1 / 100 : ℝ) * L)).trans hJlo
  have hpow : (2 : ℝ) ^ ds.length ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hlen
  have hpowB := mul_le_mul_of_nonneg_right hpow (mul_nonneg hB hL)
  have hpowJ := mul_le_mul_of_nonneg_right hpow hJ
  obtain ⟨hl, hu⟩ := movingCompensationTargets_mem_bounds J (B * L) ds hJ (mul_nonneg hB hL) hd w hw
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one] at hgap
  have hCL : 0 ≤ C * L := mul_nonneg hC hL
  have hcost : (2 : ℝ) ^ k * (B * L) ≤ 8 * Real.exp ((1 / 100 : ℝ) * L) := by
    dsimp only [C] at hgap hCL
    nlinarith only [hgap, hCL]
  constructor
  · nlinarith only [hl, hpowB, hcost, hJlo, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  · have hscale := mul_le_mul_of_nonneg_right hratio
      (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    have heq : Real.exp ((5 / 10000 : ℝ) * L) * Real.exp ((1 / 100 : ℝ) * L) =
        Real.exp ((105 / 10000 : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hscale
    have hJbound := mul_le_mul_of_nonneg_left hJhi (by positivity : 0 ≤ (2 : ℝ) ^ k)
    nlinarith only [hu, hpowJ, hscale, hJbound]

end Ostmann

end OAI
