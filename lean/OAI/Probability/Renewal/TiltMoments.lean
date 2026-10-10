import OAI.Probability.Renewal.Centered
import OAI.Probability.Renewal.Annuli

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

namespace AnnulusData
variable {p : PMF ℕ} {a : ℝ} (D : AnnulusData p a)

lemma mean_lower {u : ℝ} (hu : 0 < u) (hue : u ≤ D.epsilon) :
    (D.d / D.M) * u ^ (a - 1) ≤ natMean (tilt p u hu.le) := by
  let q := tilt p u hu.le
  have hM : 0 < D.M := zero_lt_one.trans D.M_one
  have h1 : Integrable (fun j : ℕ => (j : ℝ)) q.toMeasure := by
    simpa using tilt_moment_integrable p hu 1
  have hm := D.mass u hu hue u hu.le le_rfl
  have hmul := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ u⁻¹ / D.M)
  have hid : D.d * u ^ a * (u⁻¹ / D.M) = D.d / D.M * u ^ (a - 1) := by
    rw [Real.rpow_sub hu, Real.rpow_one]
    field_simp
  rw [hid] at hmul
  calc
    D.d / D.M * u ^ (a - 1) ≤ q.toMeasure.real (annulus D.M u) * (u⁻¹ / D.M) := hmul
    _ = ∫ _ in annulus D.M u, u⁻¹ / D.M ∂q.toMeasure := by simp
    _ ≤ ∫ j : ℕ in annulus D.M u, (j : ℝ) ∂q.toMeasure := by
      apply setIntegral_mono_on (integrable_const _) h1.integrableOn MeasurableSet.of_discrete
      intro j hj
      exact hj.1.le
    _ ≤ natMean q := setIntegral_le_integral h1 (ae_of_all _ (fun _ => Nat.cast_nonneg _))

lemma variance_lower {u : ℝ} (hu : 0 < u) (hue : u ≤ D.epsilon) :
    (D.d * D.beta / (2 * (2 * D.M) ^ 2)) * u ^ (a - 2) ≤ natVariance (tilt p u hu.le) := by
  let q := tilt p u hu.le
  have hM : 0 < D.M := zero_lt_one.trans D.M_one
  have h1 : Integrable (fun j : ℕ => (j : ℝ)) q.toMeasure := by
    simpa using tilt_moment_integrable p hu 1
  have h2 := tilt_moment_integrable p hu 2
  have hm := D.mass u hu hue u hu.le le_rfl
  have hb := D.atom u hu hue u hu.le le_rfl
  have hr := rectangle_variance_bound q h1 h2 (annulus D.M u) {D.b}
    ((u⁻¹ / (2 * D.M)) ^ 2) (by
      intro j hj l hl
      rw [mem_singleton_iff] at hl
      subst l
      have hh := (D.geometry u hu hue j hj).1
      have hpos : 0 ≤ u⁻¹ / (2 * D.M) := by positivity
      exact pow_le_pow_left₀ hpos hh 2)
  have hmulti := mul_le_mul_of_nonneg_right
    (mul_le_mul hm hb D.beta_pos.le measureReal_nonneg) (sq_nonneg (u⁻¹ / (2 * D.M)))
  have hh := hmulti.trans hr
  have hid : D.d * u ^ a * D.beta * (u⁻¹ / (2 * D.M)) ^ 2 =
      2 * ((D.d * D.beta / (2 * (2 * D.M) ^ 2)) * u ^ (a - 2)) := by
    rw [Real.rpow_sub hu, Real.rpow_two]
    field_simp
  rw [hid] at hh
  linarith

end AnnulusData

structure MomentData (p : PMF ℕ) (a : ℝ) where
  muLower : ℝ
  muLower_pos : 0 < muLower
  muUpper : ℝ
  muUpper_pos : 0 < muUpper
  varLower : ℝ
  varLower_pos : 0 < varLower
  varUpper : ℝ
  varUpper_pos : 0 < varUpper
  thirdUpper : ℝ
  thirdUpper_pos : 0 < thirdUpper
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mean_lower : ∀ u (hu : 0 < u), u ≤ epsilon → muLower * u ^ (a - 1) ≤ natMean (tilt p u hu.le)
  mean_upper : ∀ u (hu : 0 < u), u ≤ epsilon → natMean (tilt p u hu.le) ≤ muUpper * u ^ (a - 1)
  var_lower : ∀ u (hu : 0 < u), u ≤ epsilon → varLower * u ^ (a - 2) ≤ natVariance (tilt p u hu.le)
  var_upper : ∀ u (hu : 0 < u), u ≤ epsilon → natVariance (tilt p u hu.le) ≤ varUpper * u ^ (a - 2)
  third_upper : ∀ u (hu : 0 < u), u ≤ epsilon → natThird (tilt p u hu.le) ≤ thirdUpper * u ^ (a - 3)

lemma momentData_exists (p : PMF ℕ) {a : ℝ} (ha : 0 < a ∧ a < 1)
    (hpower : BoundedPowerInput p a) : Nonempty (MomentData p a) := by
  obtain ⟨D⟩ := annulusData_exists p ha hpower
  obtain ⟨K1, hK1, e1, he1, h1⟩ := tilt_moments_upper p ha.1 hpower 0
  obtain ⟨K2, hK2, e2, he2, h2⟩ := tilt_moments_upper p ha.1 hpower 1
  obtain ⟨K3, hK3, e3, he3, h3⟩ := tilt_moments_upper p ha.1 hpower 2
  have hM : 0 < D.M := zero_lt_one.trans D.M_one
  let ε := min D.epsilon (min e1 (min e2 (min e3 1)))
  have hε : 0 < ε := lt_min D.epsilon_pos (lt_min he1 (lt_min he2 (lt_min he3 zero_lt_one)))
  have hdeps {u : ℝ} (hue : u ≤ ε) : u ≤ D.epsilon ∧ u ≤ e1 ∧ u ≤ e2 ∧ u ≤ e3 ∧ u ≤ 1 := by
    dsimp [ε] at hue
    simpa only [le_min_iff] using hue
  refine ⟨⟨D.d / D.M, by positivity [D.d_pos], K1, hK1,
    D.d * D.beta / (2 * (2 * D.M) ^ 2), by positivity [D.d_pos, D.beta_pos],
    K2, hK2, 4 * (K3 + K1 ^ 3), by positivity, ε, hε, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu hue
    exact D.mean_lower hu (hdeps hue).1
  · intro u hu hue
    simpa [natMean] using h1 u hu (hdeps hue).2.1
  · intro u hu hue
    exact D.variance_lower hu (hdeps hue).1
  · intro u hu hue
    exact (natVariance_le_second _ (tilt_moment_integrable p hu 2)).trans (by
      have hh := h2 u hu (hdeps hue).2.2.1
      norm_num at hh
      exact hh)
  · intro u hu hue
    have hmean : natMean (tilt p u hu.le) ≤ K1 * u ^ (a - 1) := by
      simpa [natMean] using h1 u hu (hdeps hue).2.1
    have hraw : (∫ j : ℕ, (j : ℝ) ^ 3 ∂(tilt p u hu.le).toMeasure) ≤ K3 * u ^ (a - 3) := by
      have hh := h3 u hu (hdeps hue).2.2.2.1
      norm_num at hh
      exact hh
    have hpow : (u ^ (a - 1)) ^ 3 ≤ u ^ (a - 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
      apply Real.rpow_le_rpow_of_exponent_ge hu (hdeps hue).2.2.2.2
      push_cast
      linarith [ha.1]
    have hmcube := pow_le_pow_left₀ (natMean_nonneg _) hmean 3
    rw [mul_pow] at hmcube
    have hh := hmcube.trans (mul_le_mul_of_nonneg_left hpow (pow_nonneg hK1.le 3))
    have hcent := natThird_le_raw _ (tilt_moment_integrable p hu 3)
    nlinarith

end HoneycombLocal

end

end OAI
