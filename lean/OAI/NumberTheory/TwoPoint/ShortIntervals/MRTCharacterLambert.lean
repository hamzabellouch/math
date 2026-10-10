import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticCoefficients
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! An absolutely convergent Lambert-series identity for a bounded
character. The convolution is the actual zeta-character coefficient. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma mrt_character_lambert_pair_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ+ × ℕ+ => χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2 : ℕ)) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs : Summable (fun p : ℕ+ × ℕ+ => r ^ (p.1 * p.2 : ℕ)) := by
    simpa only [pow_zero, one_mul] using summable_prod_mul_pow (𝕜 := ℝ) 0 hr
  apply hs.of_norm_bounded
  intro p
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_of_le_one_left (pow_nonneg hr0 _) (χ.norm_le_one _)

lemma mrt_character_lambert_inner {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℕ+) :
    (∑' m : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d * m : ℕ)) =
      χ (d : ZMod q) * (r : ℂ) ^ (d : ℕ) / (1 - (r : ℂ) ^ (d : ℕ)) := by
  have hr : ‖(r : ℂ) ^ (d : ℕ)‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact pow_lt_one₀ hr0 hr1 d.pos.ne'
  have hi : (∑' m : ℕ+, (r : ℂ) ^ (d * m : ℕ)) =
      (r : ℂ) ^ (d : ℕ) / (1 - (r : ℂ) ^ (d : ℕ)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun m => (r : ℂ) ^ ((d : ℕ) * m))]
    simp_rw [Nat.mul_succ, pow_add, pow_mul]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hr]
    ring
  rw [tsum_mul_left, hi]
  ring

lemma mrt_character_lambert_fiber {q : ℕ} (χ : DirichletCharacter ℂ q)
    (r : ℝ) (n : ℕ+) :
    (∑ p : Nat.divisorsAntidiagonal (n : ℕ),
      χ (p.val.1 : ZMod q) * (r : ℂ) ^ (p.val.1 * p.val.2)) =
      χ.zetaMul n * (r : ℂ) ^ (n : ℕ) := by
  rw [mrt_character_zeta_coefficient, sum_mul]
  simp only [Finset.univ_eq_attach]
  rw [(n : ℕ).divisorsAntidiagonal.sum_attach
    (fun p => χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2))]
  rw [Nat.sum_divisorsAntidiagonal
    (fun d m => χ (d : ZMod q) * (r : ℂ) ^ (d * m))]
  apply sum_congr rfl
  intro d hd
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

theorem mrt_character_lambert {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ+, χ.zetaMul n * (r : ℂ) ^ (n : ℕ)) =
      ∑' d : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d : ℕ) /
        (1 - (r : ℂ) ^ (d : ℕ)) := by
  let g : ℕ+ × ℕ+ → ℂ := fun p =>
    χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2 : ℕ)
  have hg : Summable g := mrt_character_lambert_pair_summable χ hr0 hr1
  have hsig := (sigmaAntidiagonalEquivProd.summable_iff).mpr hg
  calc
    _ = ∑' n : ℕ+, ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        χ (p.val.1 : ZMod q) * (r : ℂ) ^ (p.val.1 * p.val.2) := by
      apply tsum_congr
      intro n
      rw [tsum_fintype, mrt_character_lambert_fiber]
    _ = ∑' p : ℕ+ × ℕ+, g p := by
      change (∑' n : ℕ+, ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        (g ∘ sigmaAntidiagonalEquivProd) ⟨n, p⟩) = _
      rw [← hsig.tsum_sigma]
      exact sigmaAntidiagonalEquivProd.tsum_eq g
    _ = ∑' d : ℕ+, ∑' m : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d * m : ℕ) :=
      hg.tsum_prod
    _ = _ := tsum_congr (mrt_character_lambert_inner χ hr0 hr1)

theorem mrt_character_thermal_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => χ.zetaMul n * (Real.exp (-t * n) : ℂ)) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  apply hs.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), pow_one]
  exact mul_le_mul_of_nonneg_right (mrt_character_zeta_coefficient_norm χ n)
    (Real.exp_nonneg _)

end TwoPointCorrelations

end OAI
