import Mathlib
import OAI.Probability.SphericalField.Gibbs.GaussianField

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma poissonRandomMeasureLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η :=
  countablePoissonLaw_rpow_lintegral_le _ _ hf ha ha1

lemma ennreal_rpow_le_one_add {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ≥0∞) :
    u^a ≤ 1+u := by
  by_cases h : u ≤ 1
  · exact (ENNReal.rpow_le_one h ha0).trans (le_add_right le_rfl)
  · have hu : u^a ≤ u := by simpa using ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge h) ha1
    exact hu.trans (le_add_left le_rfl)

lemma poissonRandomMeasureLaw_fractional_moment {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f g : S → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hfin : ∫⁻ x, f x ∂κ ≠ ⊤) (hgin : ∫⁻ x, (g x)^a ∂κ ≠ ⊤) :
    (∫⁻ η, (∫⁻ x, f x+g x ∂η)^a ∂poissonRandomMeasureLaw κ) ≠ ⊤ := by
  have hbound : ∀ᵐ η ∂poissonRandomMeasureLaw κ,
      (∫⁻ x, f x+g x ∂η)^a ≤ 1+(∫⁻ x, f x ∂η)+(∫⁻ x, (g x)^a ∂η) := by
    filter_upwards [poissonRandomMeasureLaw_rpow_lintegral_le κ hg ha ha1] with η hη
    rw [lintegral_add_left hf]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans
      (add_le_add (ennreal_rpow_le_one_add ha.le ha1 _) hη)
  apply ne_top_of_le_ne_top _ (lintegral_mono_ae hbound)
  rw [lintegral_add_left (f := fun η => 1+(∫⁻ x, f x ∂η)) (measurable_const.add (Measure.measurable_lintegral hf)),
    lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const,lintegral_const,measure_univ,one_mul,
    poissonRandomMeasureLaw_campbell κ hf,poissonRandomMeasureLaw_campbell κ (hg.pow_const a)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨by simp,hfin⟩,hgin⟩

lemma stableLogIntensity_of_integrable {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => b * Real.exp (-b*x) * f x)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂stableLogIntensity b) ≠ ⊤ := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hf.ennreal_ofReal]
  have he (x : ℝ) : ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (f x) =
      ENNReal.ofReal (b * Real.exp (-b*x) * f x) :=
    (ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le)).symm
  simp only [Pi.mul_apply]
  simp_rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x =>
    mul_nonneg (mul_nonneg hb (Real.exp_pos _).le) (hf0 x))).mp hi.hasFiniteIntegral).ne

lemma stableLogIntensity_small_moment {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x, (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Iic (a := 1-b) (by linarith) 0).integrable_indicator
    measurableSet_Iic).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Iic 0).indicator Real.exp x =
      b * (Iic 0).indicator (fun y => Real.exp ((1-b)*y)) x := by
    by_cases hx : x ∈ Iic 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Iic (0 : ℝ)).indicator Real.exp) hb0.le (Real.measurable_exp.indicator measurableSet_Iic)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  congr 1
  funext x
  by_cases hx : x ∈ Iic 0 <;> simp [hx]

lemma stableLogIntensity_large_moment {b a : ℝ} (hb : 0 ≤ b) (hab : a < b) :
    (∫⁻ x, (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Ioi (a := a-b) (by linarith) 0).integrable_indicator
    measurableSet_Ioi).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Ioi 0).indicator (fun y => Real.exp (a*y)) x =
      b * (Ioi 0).indicator (fun y => Real.exp ((a-b)*y)) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Ioi (0 : ℝ)).indicator (fun y => Real.exp (a*y))) hb ((measurable_const.mul measurable_id).exp.indicator measurableSet_Ioi)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  congr 1
  funext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

lemma stablePoissonTotal_fractional_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (ha0 : 0 ≤ a) (hab : a < b) :
    Integrable (fun η => (stablePoissonTotal η)^a) (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  rcases ha0.eq_or_lt with h | ha
  · rw [← h]
    simp only [Real.rpow_zero]
    exact integrable_const 1
  have hh := poissonRandomMeasureLaw_fractional_moment (stableLogIntensity b)
    (f := (Iic (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    (g := (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Iic)
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Ioi)
    ha (hab.trans hb1).le (stableLogIntensity_small_moment hb0 hb1)
  have he (x : ℝ) : ((Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x)^a =
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm x a]
    · simp [indicator_of_notMem hx,ha]
  simp_rw [he] at hh
  specialize hh (stableLogIntensity_large_moment hb0.le hab)
  have he' (x : ℝ) : (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x +
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x = ENNReal.ofReal (Real.exp x) := by
    by_cases hx : x ≤ 0 <;> simp [hx,not_lt.mpr,lt_of_not_ge]
  simp_rw [he'] at hh
  apply Integrable.mono' (integrable_toReal_of_lintegral_ne_top
      ((Measure.measurable_lintegral Real.measurable_exp.ennreal_ofReal).pow_const a).aemeasurable hh)
    ((stablePoissonTotal_measurable.pow_const a).aestronglyMeasurable)
  exact ae_of_all _ fun η => by
    simp only [stablePoissonTotal,Real.norm_eq_abs,ENNReal.toReal_rpow]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]

end SphericalPerceptron
end
end

end OAI
