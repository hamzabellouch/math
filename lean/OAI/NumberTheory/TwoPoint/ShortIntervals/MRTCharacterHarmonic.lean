import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterContinuation
import Mathlib.NumberTheory.AbelSummation

namespace OAI

/-! Ordered harmonic sums for a nonprincipal character converge to the
existing analytic L-function at one. No absolute convergence at one is used. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory Asymptotics
open scoped Classical Topology

variable {q : ℕ} [NeZero q]

lemma mrt_character_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ (0 : ZMod q) = 0 := by
  have hq : q ≠ 1 := by
    intro hq
    subst q
    apply hχ
    ext n
    have hn : n = (1 : ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  let : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  exact MulChar.map_zero χ

lemma mrt_character_Icc_zero_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) :
    (∑ n ∈ Icc 0 N, χ (n : ZMod q)) = ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp),
    Nat.cast_zero, mrt_character_zero χ hχ, zero_add, zero_add]

theorem mrt_character_harmonic_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, χ (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  let c : ℕ → ℂ := fun n => χ (n : ZMod q)
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ)
  have hc : c 0 = 0 := by simpa only [c, Nat.cast_zero] using mrt_character_zero χ hχ
  have hsum (N : ℕ) : (∑ n ∈ Icc 0 N, c n) = ∑ n ∈ Icc 1 N, χ (n : ZMod q) :=
    mrt_character_Icc_zero_eq χ hχ N
  have hdiff (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : DifferentiableAt ℝ f t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hint : LocallyIntegrableOn (deriv f) (Set.Ici (1 : ℝ)) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by norm_num : (-1 : ℂ).re < 0))).locallyIntegrableOn
  have hlim : Tendsto (fun N : ℕ => f N * ∑ n ∈ Icc 0 N, c n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (q : ℝ) * (N : ℝ)⁻¹)
    · intro N
      dsimp only [f]
      rw [norm_mul, hsum, Complex.cpow_neg_one, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      calc
        _ ≤ (N : ℝ)⁻¹ * q := mul_le_mul_of_nonneg_left
          (mrt_character_Icc_norm χ hχ N) (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ = _ := mul_comm _ _
    · simpa using Tendsto.const_mul (q : ℝ)
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hO : (fun N : ℕ => ∑ n ∈ Icc 0 N, c n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (0 : ℝ)) := by
    simpa only [hsum] using mrt_character_sum_bigO χ hχ
  have hderiv : (fun t : ℝ => deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) =O[atTop]
      (fun t : ℝ => t ^ (-2 : ℝ)) := by
    refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (-2) 0 (-2) ?_ ?_ (by norm_num)
    · have hh := isBigO_deriv_ofReal_cpow_const_atTop (-1 : ℂ)
      norm_num only [Complex.neg_re, Complex.one_re] at hh
      simpa only [f] using! hh
    · simpa only [Real.rpow_zero, Function.comp_apply] using!
        hO.comp_tendsto tendsto_nat_floor_atTop
  have ht := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc hdiff hint hlim hderiv
    (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num : (-2 : ℝ) < -1))
  have he : (0 : ℂ) - ∫ t in Set.Ioi (1 : ℝ), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n =
      DirichletCharacter.LFunction χ 1 := by
    rw [zero_sub, ← integral_neg,
      ← mrtCharacterAbelIntegral_eq_LFunction_of_pos χ hχ (by norm_num : 0 < (1 : ℂ).re)]
    simp only [mrtCharacterAbelIntegral, one_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) = mrtCharacterAbelKernel χ 1 t
    rw [show deriv f t = (-1 : ℂ) * (t : ℂ) ^ (-2 : ℂ) by
      have hh := Complex.deriv_ofReal_cpow_const
        (zero_lt_one.trans ht).ne' (by norm_num : (-1 : ℂ) ≠ 0)
      norm_num only at hh
      exact hh, hsum]
    simp only [mrtCharacterAbelKernel, mrtCharacterSummatory]
    norm_num
    ring
  rw [he] at ht
  convert ht using 1
  funext N
  have hz : (f 0) * c 0 = 0 := by rw [hc, mul_zero]
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), Nat.cast_zero, hz, zero_add,
    zero_add]
  apply sum_congr rfl
  intro n _
  simp [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]

end TwoPointCorrelations

end OAI
