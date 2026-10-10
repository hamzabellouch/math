import OAI.NumberTheory.TwoPoint.Bounds.PaddingDegreeTail
import OAI.NumberTheory.TwoPoint.Bounds.WeightedThetaError

namespace OAI

/-! The same fixed-modulus input bounds the logarithmic moment of the
reciprocal padding-divisor law, as needed for mass retained in bins. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma modFivePrimeBand_log_mass (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, Real.log p / p) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (p : ℝ)⁻¹ * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · simp only [ite_eq_left hs, deletedModFiveLogWeight]
    ring
  · simp [deletedModFiveLogWeight, hs]

theorem ModFiveThetaInput.padding_log_mass (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑ p ∈ paddingPrimeSupply E L, Real.log p / p) ≤ (3 / 4 : ℝ) * L + C := by
  obtain ⟨K, hK, herror⟩ := hP.deleted_log_error E
  let C₀ := ∑ p ∈ paddingPrimeSupply E 1, Real.log p / p
  have hC₀ : 0 ≤ C₀ := sum_nonneg (fun p _ => div_nonneg (log_nat_nonneg p) (Nat.cast_nonneg p))
  refine ⟨C₀ + 3 * K, by positivity, fun L hL => ?_⟩
  have hab : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hxp (x : ℝ) (hx : x ∈ Set.Icc (Real.exp 1) (Real.exp L)) : 0 < x :=
    (Real.exp_pos 1).trans_le hx.1
  have hh := weighted_theta_error (deletedModFiveLogWeight E false) (modFiveDensity false)
    K 1 1 (Real.exp 1) (Real.exp L) hK (by norm_num) (by norm_num) le_rfl hab
    (fun x : ℝ => x⁻¹)
    (fun x hx => (hasDerivAt_inv (hxp x hx).ne').differentiableAt)
    (fun x hx => by
      have hxn : x ≠ 0 := (hxp x hx).ne'
      have hc : ContDiffAt ℝ 2 (fun y : ℝ => y⁻¹) x := by fun_prop (disch := assumption)
      exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    (fun x hx => by rw [abs_of_pos (inv_pos.mpr (hxp x hx))]; simp)
    (fun x hx => by
      rw [(hasDerivAt_inv (hxp x hx).ne').deriv]
      simp [abs_of_pos (hxp x hx), one_div])
    (fun x hx => by
      rw [partialSum_deletedModFive]
      apply herror false x
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact he.trans hx.1)
  rw [← modFivePrimeBand_log_mass] at hh
  have hi : (∫ x in Real.exp 1..Real.exp L, x⁻¹) = L - 1 := by
    rw [integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _),
      Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  rw [hi, Real.log_exp] at hh
  norm_num [modFiveDensity] at hh
  rw [paddingPrimeSupply_split E L hL, sum_union (paddingPrimeSupply_split_disjoint E L)]
  have hu := (abs_le.mp hh).2
  change C₀ + _ ≤ _
  linarith

theorem ModFiveThetaInput.eventually_reciprocal_padding_log_mean (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p : paddingPrimeSupply E L, (4 / ((p.val : ℝ) + 4)) * Real.log p.val) ≤ 4 * L := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_log_mass E
  filter_upwards [eventually_ge_atTop (4 * C), eventually_ge_atTop (1 : ℝ)] with L hLC hL
  have hh : (∑ p : paddingPrimeSupply E L, (4 / ((p.val : ℝ) + 4)) * Real.log p.val) ≤
      4 * ∑ p ∈ paddingPrimeSupply E L, Real.log p / p := by
    rw [← sum_coe_sort _ (fun p : ℕ => Real.log p / p), mul_sum]
    apply sum_le_sum
    intro p _
    have hp : (0 : ℝ) < p.val := by exact_mod_cast (paddingPrimeSupply_prime p.property).pos
    calc
      (4 / ((p.val : ℝ) + 4)) * Real.log p.val ≤ (4 / p.val) * Real.log p.val :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) hp (by linarith)) (log_nat_nonneg p.val)
      _ = _ := by ring
  nlinarith [hbound L hL]

end TwoPointCorrelations

end OAI
