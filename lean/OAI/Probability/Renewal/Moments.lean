import OAI.Probability.Renewal.Tilt
import OAI.Probability.Renewal.GaussianCore

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma polynomial_exp_deficit {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    s ^ (n + 1) * Real.exp (-s) ≤
      (2 : ℝ) ^ (n + 1) * n.factorial * (1 - Real.exp (-s / 2)) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (s / 2) (by linarith : 0 ≤ s / 2) n)
  have hmul := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (2 : ℝ) ^ n * s * Real.exp (-s))
  have hsum : s / 2 + -s = -s / 2 := by ring
  have hid : (s / 2) ^ n * (2 ^ n * s * Real.exp (-s)) = s ^ (n + 1) * Real.exp (-s) := by
    rw [div_pow, pow_succ]; field_simp
  rw [hid] at hmul
  have hid' : Real.exp (s / 2) * (n.factorial : ℝ) * (2 ^ n * s * Real.exp (-s)) =
      2 ^ n * n.factorial * (s * Real.exp (-s / 2)) := by
    rw [← hsum, Real.exp_add]; ring
  rw [hid'] at hmul
  have hc := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (s / 2)) (Real.exp_pos (-s / 2)).le
  have he : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  rw [he] at hc
  have hlin : s * Real.exp (-s / 2) ≤ 2 * (1 - Real.exp (-s / 2)) := by nlinarith
  calc
    _ ≤ 2 ^ n * n.factorial * (s * Real.exp (-s / 2)) := hmul
    _ ≤ 2 ^ n * n.factorial * (2 * (1 - Real.exp (-s / 2))) := by gcongr
    _ = _ := by rw [pow_succ]; ring

lemma weighted_power_bound {u : ℝ} (hu : 0 < u) (j n : ℕ) :
    Real.exp (-u * (j : ℝ)) * (j : ℝ) ^ (n + 1) ≤
      ((2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1)) *
        (1 - Real.exp (-(u / 2) * (j : ℝ))) := by
  have h := polynomial_exp_deficit (mul_nonneg hu.le (Nat.cast_nonneg j)) n
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hu (n + 1))).mpr
  calc
    (Real.exp (-u * (j : ℝ)) * (j : ℝ) ^ (n + 1)) * u ^ (n + 1) =
        (u * (j : ℝ)) ^ (n + 1) * Real.exp (-(u * (j : ℝ))) := by
          rw [mul_pow, neg_mul]
          ring
    _ ≤ (2 : ℝ) ^ (n + 1) * n.factorial * (1 - Real.exp (-(u * (j : ℝ)) / 2)) := h
    _ = _ := by rw [show -(u * (j : ℝ)) / 2 = -(u / 2) * (j : ℝ) by ring]

lemma integrable_weighted_power (p : PMF ℕ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Integrable (fun j : ℕ => Real.exp (-u * (j : ℝ)) * (j : ℝ) ^ (n + 1)) p.toMeasure := by
  refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
    ((2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1)) ?_
  filter_upwards [] with j
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (weighted_power_bound hu j n).trans (mul_le_of_le_one_right (by positivity) (by linarith [Real.exp_pos (-(u / 2) * (j : ℝ))]))

lemma weighted_moment_bound (p : PMF ℕ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (∫ j : ℕ, Real.exp (-u * (j : ℝ)) * (j : ℝ) ^ (n + 1) ∂p.toMeasure) ≤
      ((2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1)) * (1 - laplace p (u / 2)) := by
  have hi := integral_mono (integrable_weighted_power p hu n)
    ((integrable_deficit p (by positivity : 0 ≤ u / 2)).const_mul
      ((2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1))) (fun j => weighted_power_bound hu j n)
  rw [integral_const_mul, deficit_integral p (by positivity)] at hi
  exact hi

lemma tilt_moment_integrable (p : PMF ℕ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Integrable (fun j : ℕ => (j : ℝ) ^ n) (tilt p u hu.le).toMeasure := by
  cases n with
  | zero => simp
  | succ n =>
    rw [integrable_tilt_iff]
    exact integrable_weighted_power p hu n

lemma laplace_small (p : PMF ℕ) {a : ℝ} (ha : 0 < a) (hpow : BoundedPowerInput p a) :
    ∃ ε > (0 : ℝ), ∀ u, 0 < u → u ≤ ε → (1 / 2 : ℝ) ≤ laplace p u := by
  rcases hpow with ⟨c, hc, C, hC, x₀, hx₀, _, hL⟩
  have hlim : Tendsto (fun u : ℝ => C * u ^ a) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const ha.le).tendsto 0).const_mul C
    simpa [Real.zero_rpow ha.ne'] using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u : ℝ in 𝓝[>] 0, C * u ^ a < 1 / 2 := hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨ε, hε, he⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨min ε x₀⁻¹, lt_min hε (inv_pos.mpr hx₀), ?_⟩
  intro u hu hue
  have hh := he ⟨hu, hue.trans (min_le_left _ _)⟩
  change C * u ^ a < 1 / 2 at hh
  have hh' := (hL u hu (hue.trans (min_le_right _ _))).2
  linarith

lemma tilt_moments_upper (p : PMF ℕ) {a : ℝ} (ha : 0 < a) (hpow : BoundedPowerInput p a)
    (n : ℕ) : ∃ K > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ u (hu : 0 < u), u ≤ ε →
      (∫ j : ℕ, (j : ℝ) ^ (n + 1) ∂(tilt p u hu.le).toMeasure) ≤ K * u ^ (a - (n + 1)) := by
  obtain ⟨ε, hε, he⟩ := laplace_small p ha hpow
  rcases hpow with ⟨c, hc, C, hC, x₀, hx₀, _, hL⟩
  refine ⟨2 * ((2 : ℝ) ^ (n + 1) * n.factorial) * C, by positivity,
    min ε x₀⁻¹, lt_min hε (inv_pos.mpr hx₀), ?_⟩
  intro u hu hue
  have hz : (1 / 2 : ℝ) ≤ laplace p u := he u hu (hue.trans (min_le_left _ _))
  have hhalf : u / 2 ≤ x₀⁻¹ := by linarith [hue.trans (min_le_right ε x₀⁻¹)]
  have hmean := weighted_moment_bound p hu n
  have hdef := (hL (u / 2) (by positivity) hhalf).2
  have hpowle : (u / 2) ^ a ≤ u ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
  have hK : 0 ≤ (2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1) := by positivity
  have hnum := hmean.trans (mul_le_mul_of_nonneg_left
    (hdef.trans (mul_le_mul_of_nonneg_left hpowle hC.le)) hK)
  rw [integral_tilt, smul_eq_mul]
  simp_rw [smul_eq_mul]
  have hinv : (laplace p u)⁻¹ ≤ 2 := by
    apply (inv_le_comm₀ (laplace_pos p hu.le) (by norm_num : (0 : ℝ) < 2)).mpr
    norm_num
    exact hz
  calc
    (laplace p u)⁻¹ * (∫ j : ℕ, Real.exp (-u * (j : ℝ)) * (j : ℝ) ^ (n + 1) ∂p.toMeasure) ≤
        2 * (((2 : ℝ) ^ (n + 1) * n.factorial / u ^ (n + 1)) * (C * u ^ a)) :=
      mul_le_mul hinv hnum (integral_nonneg (fun _ => by positivity)) (by norm_num)
    _ = _ := by rw [Real.rpow_sub hu, ← Nat.cast_add_one n, Real.rpow_natCast]; field_simp

end HoneycombLocal

end

end OAI
