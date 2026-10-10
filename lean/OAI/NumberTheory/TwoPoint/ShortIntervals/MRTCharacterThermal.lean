import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLambert
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHarmonic
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticKernel

namespace OAI

/-! The exponentially smoothed zeta-character convolution differs from
L(1,chi)/t by at most the modulus, uniformly for every positive t. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

noncomputable def mrtCharacterThermal {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑' n : ℕ+, χ.zetaMul n * (Real.exp (-t * n) : ℂ)

lemma mrt_exp_geometric_power (t : ℝ) (n : ℕ) :
    (Real.exp (-t) : ℂ) ^ n = (Real.exp (-t * n) : ℂ) := by
  norm_cast
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma mrt_exp_geometric_quotient (u : ℝ) (hu : 0 < u) :
    (Real.exp (-u) : ℂ) / (1 - (Real.exp (-u) : ℂ)) =
      1 / ((Real.exp u : ℂ) - 1) := by
  have he : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero u)
  have he1 : (Real.exp u : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)))
  rw [Real.exp_neg, Complex.ofReal_inv]
  field_simp

lemma mrt_character_thermal_lambert {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    mrtCharacterThermal χ t =
      ∑' d : ℕ+, χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1) := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  calc
    _ = ∑' n : ℕ+, χ.zetaMul n * (Real.exp (-t) : ℂ) ^ (n : ℕ) := by
      exact tsum_congr (fun n => by rw [mrt_exp_geometric_power])
    _ = ∑' d : ℕ+, χ (d : ZMod q) * (Real.exp (-t) : ℂ) ^ (d : ℕ) /
        (1 - (Real.exp (-t) : ℂ) ^ (d : ℕ)) :=
      mrt_character_lambert χ (Real.exp_nonneg _) he
    _ = _ := by
      apply tsum_congr
      intro d
      rw [mrt_exp_geometric_power]
      have hu : 0 < t * (d : ℕ) := mul_pos ht (by exact_mod_cast d.pos)
      have hh := mrt_exp_geometric_quotient (t * (d : ℕ)) hu
      have hn : -t * (d : ℕ) = -(t * (d : ℕ)) := by ring
      rw [hn]
      calc
        _ = χ (d : ZMod q) * ((Real.exp (-(t * (d : ℕ))) : ℂ) /
            (1 - (Real.exp (-(t * (d : ℕ))) : ℂ))) := by ring
        _ = _ := by rw [hh]; ring

lemma mrt_character_thermal_lambert_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun d : ℕ+ => χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1)) := by
  have hs := (mrt_character_lambert_pair_summable χ (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))).prod
  apply hs.congr
  intro d
  rw [mrt_character_lambert_inner χ (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))]
  rw [mrt_exp_geometric_power]
  have hu : 0 < t * (d : ℕ) := mul_pos ht (by exact_mod_cast d.pos)
  have hh := mrt_exp_geometric_quotient (t * (d : ℕ)) hu
  have hn : -t * (d : ℕ) = -(t * (d : ℕ)) := by ring
  rw [hn]
  calc
    _ = χ (d : ZMod q) * ((Real.exp (-(t * (d : ℕ))) : ℂ) /
        (1 - (Real.exp (-(t * (d : ℕ))) : ℂ))) := by ring
    _ = _ := by rw [hh]; ring

lemma mrt_sum_positive_range (f : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ n ∈ Icc 1 N, f n := by
  rw [range_eq_Ico, sum_Ico_add' f 0 N 1]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem mrt_character_thermal_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {t : ℝ} (ht : 0 < t) :
    ‖DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t‖ ≤ q := by
  let a : ℕ → ℂ := fun i => χ ((i + 1 : ℕ) : ZMod q)
  have hA (N : ℕ) : ‖∑ i ∈ range N, a i‖ ≤ q := by
    change ‖∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q)‖ ≤ q
    rw [mrt_sum_positive_range (fun n => χ (n : ZMod q)) N]
    exact mrt_character_Icc_norm χ hχ N
  have hfinite (N : ℕ) :
      ‖(∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) / (t : ℂ) -
        ∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) /
          ((Real.exp (t * (i + 1 : ℕ)) : ℂ) - 1)‖ ≤ q := by
    have hh := mrt_quadratic_remainder_weighted_prefix a (Nat.cast_nonneg q) ht hA N
    convert hh using 1
    congr 1
    rw [sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [mrtQuadraticRemainder, a, Complex.ofReal_sub, Complex.ofReal_inv,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one]
    simp only [mul_inv_rev]
    ring
  have hharm : Tendsto (fun N : ℕ =>
      (∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) / (t : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1 / (t : ℂ))) := by
    have he (N : ℕ) : (∑ i ∈ range N,
        χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) =
        ∑ n ∈ Icc 1 N, χ (n : ZMod q) / (n : ℂ) :=
      mrt_sum_positive_range (fun n => χ (n : ZMod q) / (n : ℂ)) N
    simpa only [he] using (mrt_character_harmonic_tendsto χ hχ).div_const (t : ℂ)
  have hs := (summable_pnat_iff_summable_succ (f := fun d : ℕ =>
    χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1))).mp
      (mrt_character_thermal_lambert_summable χ ht)
  have hlam : Tendsto (fun N : ℕ => ∑ i ∈ range N,
      χ ((i + 1 : ℕ) : ZMod q) / ((Real.exp (t * (i + 1 : ℕ)) : ℂ) - 1))
      atTop (𝓝 (mrtCharacterThermal χ t)) := by
    rw [mrt_character_thermal_lambert χ ht,
      tsum_pnat_eq_tsum_succ (f := fun d => χ (d : ZMod q) /
        ((Real.exp (t * d) : ℂ) - 1))]
    exact hs.hasSum.tendsto_sum_nat
  exact le_of_tendsto' ((hharm.sub hlam).norm) hfinite

end TwoPointCorrelations

end OAI
