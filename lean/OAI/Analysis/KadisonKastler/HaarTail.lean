import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The geometric-polynomial tail in scalar recovery

The normalization here uses angular Haar measure `dt / (2 * pi)`.
-/

namespace KadisonKastler

open scoped BigOperators Interval
open MeasureTheory

noncomputable section

/-- The sum of the first `N` positive powers on the circle. -/
def haarGeometricSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (t : ℂ)) ^ (k + 1)

/-- The normalized polynomial used in the Haar tail estimate. -/
def haarPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  (Real.sqrt (N : ℝ))⁻¹ • haarGeometricSum N t

theorem haarGeometricSum_eq_sum_exp (N : ℕ) (t : ℝ) :
    haarGeometricSum N t =
      ∑ k ∈ Finset.range N,
        Complex.exp (Complex.I * (((k + 1 : ℕ) : ℝ) * t : ℝ)) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The chord of the circle is bounded below linearly on the principal arc. -/
theorem haar_chord_lower_bound {t : ℝ} (ht : |t| ≤ Real.pi) :
    2 * |t| / Real.pi ≤ ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have h := Real.mul_abs_le_abs_sin (x := t / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have heq : 2 / Real.pi * (|t| / 2) = |t| / Real.pi := by ring
  rw [heq] at h
  calc
    _ = 2 * (|t| / Real.pi) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The geometric identity gives a numerator of norm at most two. -/
theorem haarGeometricSum_mul_chord_le (N : ℕ) (t : ℝ) :
    ‖haarGeometricSum N t‖ * ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ 2 := by
  let z := Complex.exp (Complex.I * (t : ℂ))
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal t
  have heq : haarGeometricSum N t * (z - 1) = z * (z ^ N - 1) := by
    dsimp [haarGeometricSum]
    simp_rw [pow_succ']
    rw [← Finset.mul_sum, mul_assoc, geom_sum_mul]
  calc
    _ = ‖z * (z ^ N - 1)‖ := by rw [← norm_mul, heq]
    _ = ‖z ^ N - 1‖ := by rw [norm_mul, hz, one_mul]
    _ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [norm_pow, hz]; norm_num

/-- The precise pointwise estimate from the manuscript. -/
theorem norm_haarGeometricSum_le {N : ℕ} {t : ℝ}
    (ht0 : 0 < |t|) (htpi : |t| ≤ Real.pi) :
    ‖haarGeometricSum N t‖ ≤ Real.pi / |t| := by
  have hc := haar_chord_lower_bound htpi
  have hn := haarGeometricSum_mul_chord_le N t
  have hmul := mul_le_mul_of_nonneg_left hc (norm_nonneg (haarGeometricSum N t))
  apply (le_div_iff₀ ht0).2
  have hpi := Real.pi_pos
  have h := hmul.trans hn
  field_simp at h
  nlinarith

theorem haarPolynomial_norm_sq_le {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht0 : 0 < |t|) (htpi : |t| ≤ Real.pi) :
    ‖haarPolynomial N t‖ ^ 2 ≤ Real.pi ^ 2 / ((N : ℝ) * t ^ 2) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hb := norm_haarGeometricSum_le (N := N) ht0 htpi
  have ht : t ≠ 0 := by simpa using ne_of_gt ht0
  have hbound : ‖haarGeometricSum N t‖ ^ 2 ≤ (Real.pi / |t|) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  simp only [haarPolynomial, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
  calc
    _ ≤ ((Real.sqrt (N : ℝ)) ^ 2)⁻¹ * (Real.pi / |t|) ^ 2 :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 (sq_nonneg _))
    _ = _ := by rw [hsq, div_pow, habs]; field_simp

theorem continuous_haarGeometricSum (N : ℕ) : Continuous (haarGeometricSum N) := by
  unfold haarGeometricSum
  fun_prop

theorem continuous_haarPolynomial (N : ℕ) : Continuous (haarPolynomial N) := by
  unfold haarPolynomial
  exact (continuous_const : Continuous (fun _ : ℝ => (Real.sqrt (N : ℝ))⁻¹)).smul
    (continuous_haarGeometricSum N)

theorem norm_haarGeometricSum_le_card (N : ℕ) (t : ℝ) :
    ‖haarGeometricSum N t‖ ≤ (N : ℝ) := by
  unfold haarGeometricSum
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖Complex.exp (Complex.I * (t : ℂ)) ^ (k + 1)‖ :=
      norm_sum_le _ _
    _ = _ := by simp [norm_pow]

theorem norm_haarPolynomial_le_sqrt {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖haarPolynomial N t‖ ≤ Real.sqrt (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := Real.sqrt_pos.2 hNr
  simp only [haarPolynomial, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (norm_haarGeometricSum_le_card N t) (inv_nonneg.2 hs.le)
    _ = (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by
      rw [Real.mul_self_sqrt hNr.le]
    _ = _ := inv_mul_cancel_left₀ hs.ne' _

theorem haarGeometricSum_neg (N : ℕ) (t : ℝ) :
    haarGeometricSum N (-t) = star (haarGeometricSum N t) := by
  simp only [haarGeometricSum, star_sum, star_pow]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  change Complex.exp (Complex.I * ((-t : ℝ) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ)))
  rw [← Complex.exp_conj]
  simp

theorem norm_haarPolynomial_neg (N : ℕ) (t : ℝ) :
    ‖haarPolynomial N (-t)‖ = ‖haarPolynomial N t‖ := by
  simp only [haarPolynomial, norm_smul, haarGeometricSum_neg, norm_star]

/-- The normalized angular integral outside the symmetric arc of radius `a`. -/
def haarTailEnergy (N : ℕ) (a : ℝ) : ℝ :=
  ((∫ t in min a Real.pi..Real.pi, ‖haarPolynomial N t‖ ^ 2) +
    ∫ t in -Real.pi..-min a Real.pi, ‖haarPolynomial N t‖ ^ 2) / (2 * Real.pi)

theorem haarTailEnergy_eq (N : ℕ) (a : ℝ) :
    haarTailEnergy N a =
      (∫ t in min a Real.pi..Real.pi, ‖haarPolynomial N t‖ ^ 2) / Real.pi := by
  have h := intervalIntegral.integral_comp_neg
    (fun t => ‖haarPolynomial N t‖ ^ 2) (a := min a Real.pi) (b := Real.pi)
  simp only [norm_haarPolynomial_neg] at h
  unfold haarTailEnergy
  rw [← h]
  ring

theorem haarTailEnergy_nonneg (N : ℕ) (a : ℝ) : 0 ≤ haarTailEnergy N a := by
  rw [haarTailEnergy_eq]
  exact div_nonneg
    (intervalIntegral.integral_nonneg_of_forall (min_le_right _ _) (fun t => sq_nonneg _))
    Real.pi_pos.le

theorem haarTailEnergy_of_pi_le (N : ℕ) {a : ℝ} (ha : Real.pi ≤ a) :
    haarTailEnergy N a = 0 := by
  simp [haarTailEnergy, min_eq_right ha]

/-- Integration of the square geometric bound away from its singular point. -/
theorem integral_haarPolynomial_norm_sq_le {N : ℕ} (hN : 0 < N)
    {a : ℝ} (ha : 0 < a) (hapi : a ≤ Real.pi) :
    (∫ t in a..Real.pi, ‖haarPolynomial N t‖ ^ 2) ≤
      Real.pi ^ 2 / (N : ℝ) * (a⁻¹ - Real.pi⁻¹) := by
  have hz : (0 : ℝ) ∉ Set.uIcc a Real.pi :=
    Set.notMem_uIcc_of_lt ha Real.pi_pos
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) volume a Real.pi :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hz)
  have heval : (∫ t : ℝ in a..Real.pi, t ^ (-2 : ℤ)) =
      a⁻¹ - Real.pi⁻¹ := by
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  calc
    _ ≤ ∫ t : ℝ in a..Real.pi, (Real.pi ^ 2 / (N : ℝ)) * t ^ (-2 : ℤ) := by
      apply intervalIntegral.integral_mono_on hapi
        (((continuous_haarPolynomial N).norm.pow 2).intervalIntegrable a Real.pi)
        (hi.const_mul _)
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      have h := haarPolynomial_norm_sq_le hN
        (show 0 < |t| by rwa [abs_of_pos ht0])
        (show |t| ≤ Real.pi by simpa [abs_of_pos ht0] using ht.2)
      simpa [zpow_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    _ = _ := by rw [intervalIntegral.integral_const_mul, heval]

theorem haarTailEnergy_le {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    haarTailEnergy N a ≤ Real.pi / ((N : ℝ) * a) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases hapi : a ≤ Real.pi
  · rw [haarTailEnergy_eq, min_eq_left hapi]
    have h := integral_haarPolynomial_norm_sq_le hN ha hapi
    have hdiv := div_le_div_of_nonneg_right h Real.pi_pos.le
    calc
      _ ≤ (Real.pi ^ 2 / (N : ℝ) * (a⁻¹ - Real.pi⁻¹)) / Real.pi := hdiv
      _ ≤ Real.pi / ((N : ℝ) * a) := by
        have heq : (Real.pi ^ 2 / (N : ℝ) * (a⁻¹ - Real.pi⁻¹)) / Real.pi =
            Real.pi / ((N : ℝ) * a) - (N : ℝ)⁻¹ := by
          field_simp
        rw [heq]
        exact sub_le_self _ (inv_nonneg.2 hNr.le)
  · rw [haarTailEnergy_of_pi_le N (le_of_not_ge hapi)]
    positivity

/-- The Haar tail bound at arc radius `R/N`, with the manuscript's constant. -/
theorem haarTailEnergy_div_le {N : ℕ} (hN : 0 < N) {R : ℝ} (hR : 0 < R) :
    haarTailEnergy N (R / (N : ℝ)) ≤ Real.pi / R := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  convert haarTailEnergy_le hN (div_pos hR hNr) using 1
  congr 1
  field_simp

end

end KadisonKastler

end OAI
