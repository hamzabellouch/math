import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound

namespace OAI

/-! # Half-Gaussian velocity moments for the hot weight and cold cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.VelocityMoment

def weight (v : Velocity) : ℝ := Real.exp (‖v‖^2/2)
def moment (f : Velocity → ℝ) : ℝ≥0∞ := ∫⁻ v, ENNReal.ofReal (weight v*f v)

theorem weight_pos (v : Velocity) : 0 < weight v := Real.exp_pos _
theorem weight_one_le (v : Velocity) : 1 ≤ weight v := Real.one_le_exp (by positivity)
theorem weight_le (v : Velocity) : weight v ≤ Real.exp (2*‖v‖^2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem moment_mono {f g : Velocity → ℝ} (h : ∀ v, f v ≤ g v) : moment f ≤ moment g :=
  lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (h v) (weight_pos v).le))

theorem moment_mono_ae {f g : Velocity → ℝ} (h : ∀ᵐ v, f v ≤ g v) : moment f ≤ moment g := by
  apply lintegral_mono_ae
  filter_upwards [h] with v hv
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hv (weight_pos v).le)

theorem weight_H_le (q : ℝ) (v : Velocity) :
    weight v*H q v ≤ gaussianMajorant (1/2) q v := by
  calc
    _ ≤ weight v*gaussianMajorant 1 q v :=
      mul_le_mul_of_nonneg_left (H_le_gaussianMajorant q v) (weight_pos v).le
    _ = _ := by
      unfold weight gaussianMajorant
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem weight_H_integrable {q : ℝ} (hq : q < 2) :
    Integrable (fun v => weight v*H q v) := by
  apply (integrable_gaussianMajorant (by norm_num : (0:ℝ) < 1/2) hq).mono'
    (by unfold weight H singularity; fun_prop)
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (mul_nonneg (weight_pos v).le (H_nonneg q v))]
  exact weight_H_le q v

def hotConstant (q : ℝ) : ℝ := ∫ v, weight v*H q v

theorem hotConstant_nonneg (q : ℝ) : 0 ≤ hotConstant q :=
  integral_nonneg (fun v => mul_nonneg (weight_pos v).le (H_nonneg q v))

theorem hot_moment {q a : ℝ} (hq : q < 2) (ha : 0 ≤ a) :
    moment (fun v => a*H q v) = ENNReal.ofReal (a*hotConstant q) := by
  have hi := (weight_H_integrable hq).const_mul a
  unfold moment hotConstant
  simp_rw [show ∀ v : Velocity, weight v*(a*H q v) = a*(weight v*H q v) by intro v; ring]
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul]
  · exact ae_of_all _ (fun v => mul_nonneg ha (mul_nonneg (weight_pos v).le (H_nonneg q v)))

theorem moment_add {f g : Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    moment (fun v => f v+g v) = moment f+moment g := by
  unfold moment
  simp_rw [mul_add,ENNReal.ofReal_add (mul_nonneg (weight_pos _).le (hf _))
    (mul_nonneg (weight_pos _).le (hg _))]
  apply lintegral_add_left
  have hm : Measurable (fun v => ENNReal.ofReal (weight v*f v)) := by
    unfold weight
    fun_prop
  exact hm

theorem moment_le_exponential {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) :
    moment f ≤ SheetClass.exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) := by
  rw [SheetClass.exponentialMoment_density hfm]
  exact lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (weight_le v) (hf v)))

theorem density_integrable {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hb : moment f ≤ ENNReal.ofReal M) :
    Integrable f := by
  have hi : Integrable (fun v => weight v*f v) := by
    refine ⟨by unfold weight; fun_prop,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _
      (fun v => mul_nonneg (weight_pos v).le (hf v)))).mpr (hb.trans_lt ENNReal.ofReal_lt_top)
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (hf v)]
  exact le_mul_of_one_le_left (hf v) (weight_one_le v)

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
