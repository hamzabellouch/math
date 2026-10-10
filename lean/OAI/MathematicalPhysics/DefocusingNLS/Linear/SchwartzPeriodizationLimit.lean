import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPhysicalSampling
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-! # Fixed Schwartz samples converge locally as the torus expands -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_schwartz_periodization (ψ : 𝓢(E, ℂ)) (y : E)
    (L : ℕ → ℝ) (hL : ∀ j, 1 ≤ L j) (hLinf : Tendsto L atTop atTop) :
    Tendsto (fun j => ∑' n : frequencyLattice, ψ (y + (2 * Real.pi * L j) • (n : E)))
      atTop (𝓝 (ψ y)) := by
  classical
  let M : ℝ := 2 ^ (14 : ℕ) *
    (Finset.Iic (14, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdecay (x : E) : (1 + ‖x‖) ^ 14 * ‖ψ x‖ ≤ M := by
    simpa only [M, norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (14, 0)) (k := 14) (n := 0) (by decide) (by decide) ψ x
  let bound := fun n : frequencyLattice => M * ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹
  have hs : Summable bound := by
    have h := summable_sobolev_variances 0 7 (by norm_num)
    have hh : Summable (fun n : frequencyLattice => ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹) := by
      convert h using 1
      ext n
      norm_num [Real.rpow_neg]
    exact hh.mul_left M
  have htriangle (j : ℕ) (n : frequencyLattice) :
      (2 * Real.pi * ‖n‖) * L j - ‖y‖ ≤ ‖y + (2 * Real.pi * L j) • (n : E)‖ := by
    have ht := norm_sub_le (y + (2 * Real.pi * L j) • (n : E)) y
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * Real.pi * L j by positivity [hL j]), Submodule.norm_coe] at ht
    nlinarith
  have hp (n : frequencyLattice) :
      Tendsto (fun j => ψ (y + (2 * Real.pi * L j) • (n : E))) atTop
        (𝓝 (if n = 0 then ψ y else 0)) := by
    by_cases hn : n = 0
    · subst n
      simpa only [ite_true, Submodule.coe_zero, smul_zero, add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ y) atTop (𝓝 (ψ y)))
    · have hnpos : 0 < 2 * Real.pi * ‖n‖ := by
        positivity [lt_of_lt_of_le zero_lt_one (one_le_norm_frequencyLattice hn)]
      have hnorm : Tendsto (fun j => ‖y + (2 * Real.pi * L j) • (n : E)‖) atTop atTop :=
        tendsto_atTop_mono (fun j => htriangle j n)
          (by simpa only [sub_eq_add_neg] using
            tendsto_atTop_add_const_right atTop (-‖y‖) (hLinf.const_mul_atTop hnpos))
      have he : Tendsto (fun j => y + (2 * Real.pi * L j) • (n : E)) atTop (cocompact E) := by
        simpa only [Metric.cobounded_eq_cocompact] using
          (tendsto_norm_atTop_iff_cobounded.mp hnorm)
      rw [ite_eq_right hn]
      exact (SchwartzMap.tendsto_cocompact ψ).comp he
  have hb : ∀ᶠ j in atTop, ∀ n : frequencyLattice,
      ‖ψ (y + (2 * Real.pi * L j) • (n : E))‖ ≤ bound n := by
    filter_upwards [hLinf.eventually (eventually_ge_atTop ‖y‖)] with j hj n
    have hnorm : ‖n‖ ≤ ‖y + (2 * Real.pi * L j) • (n : E)‖ := by
      by_cases hn : n = 0
      · simp only [hn, norm_zero]
        positivity
      · have hn1 := one_le_norm_frequencyLattice hn
        have hp := Real.pi_gt_three
        have hLj := hL j
        have hprod := mul_le_mul_of_nonneg_left hLj
          (mul_nonneg (by linarith : 0 ≤ 2 * Real.pi - 1) (norm_nonneg n))
        have hyprod := mul_le_mul_of_nonneg_left hj (by linarith : 0 ≤ ‖n‖)
        nlinarith [htriangle j n]
    have hw : (1 + ‖n‖ ^ 2) ^ (7 : ℕ) ≤
        (1 + ‖y + (2 * Real.pi * L j) • (n : E)‖) ^ 14 := by
      calc
        _ ≤ ((1 + ‖y + (2 * Real.pi * L j) • (n : E)‖) ^ 2) ^ (7 : ℕ) := by
          gcongr
          calc
            1 + ‖n‖ ^ 2 ≤ (1 + ‖n‖) ^ 2 := by nlinarith [norm_nonneg n]
            _ ≤ (1 + ‖y + (2 * Real.pi * L j) • (n : E)‖) ^ 2 := by gcongr
        _ = _ := by ring
    change _ ≤ M * ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (1 + ‖y + (2 * Real.pi * L j) • (n : E)‖) ^ 14 *
          ‖ψ (y + (2 * Real.pi * L j) • (n : E))‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hw (norm_nonneg
          (ψ (y + (2 * Real.pi * L j) • (n : E))))]
      _ ≤ M := hdecay _
  have h := tendsto_tsum_of_dominated_convergence hs hp hb
  simpa only [tsum_ite_eq] using h

end DefocusingNLS

end OAI
