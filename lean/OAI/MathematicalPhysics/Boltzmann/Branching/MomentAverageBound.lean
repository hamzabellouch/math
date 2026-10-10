import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityPolynomialBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions

namespace OAI

section

/-! # Cutoff-independent loss frequency from the half-Gaussian moment -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

theorem weighted_integrable {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hb : moment f ≤ ENNReal.ofReal M) :
    Integrable (fun v => weight v*f v) := by
  refine ⟨by unfold weight; fun_prop,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _
    (fun v => mul_nonneg (weight_pos v).le (hf v)))).mpr (hb.trans_lt ENNReal.ofReal_lt_top)

theorem weighted_integral_le {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M)
    (hb : moment f ≤ ENNReal.ofReal M) : (∫ v, weight v*f v) ≤ M := by
  have hi := weighted_integrable hfm hf hb
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun v => mul_nonneg (weight_pos v).le (hf v)))
  change (∫⁻ v, ENNReal.ofReal (weight v*f v)) ≤ ENNReal.ofReal M at hb
  rw [← he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hb

theorem frequency_le_moment (b : ℝ) {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M)
    (hb : moment f ≤ ENNReal.ofReal M) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤ 2*Real.pi*(‖v‖+1)*M := by
  have hi := (weighted_integrable hfm hf hb).const_mul (‖v‖+1)
  have hdom (w : Velocity) : CollisionCutoff.rate b v w*f w ≤
      (‖v‖+1)*(weight w*f w) := by
    have hr : CollisionCutoff.rate b v w ≤ ‖v-w‖ := by
      unfold CollisionCutoff.rate
      split_ifs <;> simp only [le_refl,norm_nonneg]
    have hw : ‖v-w‖ ≤ (‖v‖+1)*weight w := by
      have hn := norm_sub_le v w
      have hv := mul_le_mul_of_nonneg_left (weight_one_le w) (norm_nonneg v)
      nlinarith [norm_le_weight w]
    calc
      _ ≤ ‖v-w‖*f w := mul_le_mul_of_nonneg_right hr (hf w)
      _ ≤ ((‖v‖+1)*weight w)*f w := mul_le_mul_of_nonneg_right hw (hf w)
      _ = _ := by ring
  have hfi : Integrable (fun w => CollisionCutoff.rate b v w*f w) := by
    apply hi.mono' ((CollisionCutoff.measurable_rate b v).mul hfm).aestronglyMeasurable
    exact ae_of_all _ (fun w => by
      change ‖CollisionCutoff.rate b v w*f w‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))]
      exact hdom w)
  have hle := integral_mono hfi hi hdom
  rw [integral_const_mul] at hle
  have hmoment := weighted_integral_le hfm hf hM hb
  unfold CollisionCutoff.frequency
  calc
    _ ≤ 2*Real.pi*((‖v‖+1)*(∫ w, weight w*f w)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ 2*Real.pi*((‖v‖+1)*M) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmoment (by positivity)) (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.VelocityMoment

end

end

section

/-! # Scalar velocity averages bounded by the half-Gaussian moment -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

theorem mass_lintegral_le_moment {f : Velocity → ℝ} (hf : ∀ v, 0 ≤ f v) :
    (∫⁻ v, ENNReal.ofReal (f v)) ≤ moment f := by
  apply lintegral_mono
  intro v
  apply ENNReal.ofReal_le_ofReal
  exact le_mul_of_one_le_left (hf v) (weight_one_le v)

theorem integrable_of_moment_bound {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : moment f ≤ ENNReal.ofReal M) :
    Integrable f := by
  refine ⟨hfm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf)).mpr
  exact ((mass_lintegral_le_moment hf).trans hM).trans_lt ENNReal.ofReal_lt_top

theorem integral_le_of_moment_bound {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM0 : 0 ≤ M)
    (hM : moment f ≤ ENNReal.ofReal M) : (∫ v, f v) ≤ M := by
  have hi := integrable_of_moment_bound hfm hf hM
  apply (ENNReal.ofReal_le_ofReal_iff hM0).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf)]
  exact (mass_lintegral_le_moment hf).trans hM

theorem average_le_of_moment_bound {f ψ : Velocity → ℝ} {C M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hC : 0 ≤ C) (hM0 : 0 ≤ M)
    (hM : moment f ≤ ENNReal.ofReal M) (hψ : ∀ v, |ψ v| ≤ C) :
    |∫ v, ψ v*f v| ≤ C*M := by
  have hi := integrable_of_moment_bound hfm hf hM
  have hb : ∀ᵐ v, ‖ψ v*f v‖ ≤ C*f v := ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hf v)]
    exact mul_le_mul_of_nonneg_right (hψ v) (hf v))
  have havg := norm_integral_le_of_norm_le (hi.const_mul C) hb
  rw [integral_const_mul,Real.norm_eq_abs] at havg
  exact havg.trans (mul_le_mul_of_nonneg_left (integral_le_of_moment_bound hfm hf hM0 hM) hC)

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
