import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem one_add_abs_pow_le_two_exp (x : ℝ) (p : ℕ) :
    (1 + |x|) ^ p ≤ Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x) := by
  calc
    (1 + |x|) ^ p ≤ (Real.exp |x|) ^ p := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp |x|
    _ = Real.exp ((p : ℝ) * |x|) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [abs_of_nonpos hx, mul_neg, neg_mul]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)

theorem integrable_one_add_abs_pow_gaussian (p : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (p : ℝ)).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(p : ℝ)))).mono'
  · fun_prop
  · filter_upwards [] with x
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |x|) ^ p)]
      using one_add_abs_pow_le_two_exp x p

theorem integral_one_add_abs_pow_gaussian_le {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) ≤ Real.exp (2 * (p : ℝ) ^ 2) := by
  have hpos := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (p : ℝ)
  have hneg := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(p : ℝ))
  have hmgf (r : ℝ) : (∫ x : ℝ, Real.exp (r * x) ∂gaussianReal 0 1) =
      Real.exp (r ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) r
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : 2 ≤ Real.exp (3 * (p : ℝ) ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (3 * (p : ℝ) ^ 2 / 2), sq_nonneg ((p : ℝ) - 1)]
  calc
    (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) ≤
        ∫ x : ℝ, Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x)
          ∂gaussianReal 0 1 :=
      integral_mono (integrable_one_add_abs_pow_gaussian p) (hpos.add hneg)
        (fun x => one_add_abs_pow_le_two_exp x p)
    _ = 2 * Real.exp ((p : ℝ) ^ 2 / 2) := by
      rw [integral_add hpos hneg, hmgf, hmgf, neg_sq]
      ring
    _ ≤ Real.exp (3 * (p : ℝ) ^ 2 / 2) * Real.exp ((p : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (2 * (p : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem abs_gaussian_observation_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |t + Real.sqrt t * x| ≤ Real.sqrt t * (1 + |x|) := by
  calc
    |t + Real.sqrt t * x| ≤ |t| + |Real.sqrt t * x| := abs_add_le _ _
    _ = t + Real.sqrt t * |x| := by rw [abs_of_nonneg ht, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg t)]
    _ ≤ Real.sqrt t + Real.sqrt t * |x| :=
      add_le_add_left (Real.le_sqrt_self_iff.mpr ht1) _
    _ = Real.sqrt t * (1 + |x|) := by ring

theorem integrable_gaussian_observation_abs_pow {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : ℕ) :
    Integrable (fun x : ℝ => |t + Real.sqrt t * x| ^ p) (gaussianReal 0 1) := by
  apply ((integrable_one_add_abs_pow_gaussian p).const_mul (Real.sqrt t ^ p)).mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_gaussian_observation_le ht ht1 x) p

theorem integral_gaussian_observation_abs_pow_le {t : ℝ} {p : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hp : 1 ≤ p) :
    (∫ x : ℝ, |t + Real.sqrt t * x| ^ p ∂gaussianReal 0 1) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
  have hscale : Real.sqrt t ^ p ≤ t ^ ((p : ℝ) / 4) := by
    calc
      Real.sqrt t ^ p = t ^ ((p : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
        congr 1
        ring
      _ ≤ t ^ ((p : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by have : 0 ≤ (p : ℝ) := Nat.cast_nonneg p; linarith)
  calc
    (∫ x : ℝ, |t + Real.sqrt t * x| ^ p ∂gaussianReal 0 1) ≤
        ∫ x : ℝ, Real.sqrt t ^ p * (1 + |x|) ^ p ∂gaussianReal 0 1 := by
      apply integral_mono (integrable_gaussian_observation_abs_pow ht.le ht1 p)
        ((integrable_one_add_abs_pow_gaussian p).const_mul _)
      intro x
      change |t + Real.sqrt t * x| ^ p ≤ Real.sqrt t ^ p * (1 + |x|) ^ p
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_gaussian_observation_le ht.le ht1 x) p
    _ = Real.sqrt t ^ p * (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) :=
      integral_const_mul _ _
    _ ≤ Real.sqrt t ^ p * Real.exp (2 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_one_add_abs_pow_gaussian_le hp) (by positivity)
    _ ≤ t ^ ((p : ℝ) / 4) * Real.exp (2 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (Real.exp_nonneg _)
    _ = Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := mul_comm _ _

theorem integrable_gaussian_observation_abs_pow_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : ℕ) :
    Integrable (fun ω => |t + Real.sqrt t * G ω| ^ p) μ := by
  have h := integrable_gaussian_observation_abs_pow ht ht1 p
  rw [← hG.map_eq] at h
  exact h.comp_aemeasurable hG.aemeasurable

theorem integral_gaussian_observation_abs_pow_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) {t : ℝ} {p : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hp : 1 ≤ p) :
    (∫ ω, |t + Real.sqrt t * G ω| ^ p ∂μ) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
  have heq := hG.integral_comp
    (f := fun x : ℝ => |t + Real.sqrt t * x| ^ p) (by fun_prop)
  change (∫ ω, |t + Real.sqrt t * G ω| ^ p ∂μ) = _ at heq
  rw [heq]
  exact integral_gaussian_observation_abs_pow_le ht ht1 hp

end Problem367

end

end OAI
