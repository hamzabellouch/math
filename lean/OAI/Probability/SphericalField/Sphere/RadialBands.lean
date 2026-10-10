import Mathlib
import OAI.Probability.SphericalField.Perceptron.TimeLaw
import OAI.Probability.SphericalField.Sphere.Invariance
import OAI.Probability.SphericalField.Sphere.RadialDensity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma canonicalRadial_band_mass_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) ∧
    (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2)) := by
  have hm := normSquareBand_measurable n ε
  have hlo : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn
      (canonicalRadialDensity_integrable n hb).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).1)
      (canonicalRadialDensity_pos n 1 x).le
  have hup : (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      (canonicalRadialDensity_integrable n hb).integrableOn
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).2)
      (canonicalRadialDensity_pos n 1 x).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hhalf (Real.exp_pos (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))).le
    have h' : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
        Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
        (canonicalRadialMass n 1).real (normSquareBand n ε) := by simpa only [mul_one_div] using h
    exact h'.trans hlo
  · apply hup.trans
    exact mul_le_of_le_one_right (Real.exp_pos _).le (measureReal_le_one)

lemma canonicalRadial_band_log_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    (1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ) ≤
      Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ∧
    Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ≤
      (1-b)/2+|1-b| *ε/2 := by
  obtain ⟨hl,hu⟩ := canonicalRadial_band_mass_bounds n hb hhalf
  have hlpos : 0 < Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 := by positivity
  have hmpos := hlpos.trans_le hl
  have hl' := Real.log_le_log hlpos hl
  have hu' := Real.log_le_log hmpos hu
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0),Real.log_exp] at hl'
  rw [Real.log_exp] at hu'
  have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  constructor
  · apply (le_div_iff₀ hn).mpr
    have he : ((1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ))*((n+1 : ℕ) : ℝ) =
        ((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2)-Real.log 2 := by field_simp
    rw [he]
    exact hl'
  · exact (div_le_iff₀ hn).mpr (by nlinarith)

lemma canonicalRadial_band_log_eventually {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      (1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ) ≤
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ∧
      Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ≤
        (1-b)/2+|1-b| *ε/2 :=
  (canonicalRadial_band_eventually_half hε hε1).mono fun n hn => canonicalRadial_band_log_bounds n hb hn

lemma unitSphere_continuous_integrable {n : ℕ}
    {f : Metric.sphere (0 : Spin (n+1)) 1 → ℝ} (hf : Continuous f) :
    Integrable f (unitSphereLaw (n+1)) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun u => hC u (mem_univ _))

def sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) : ℝ :=
  ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.exp (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma sphericalExp_even (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z (-r) = sphericalExp n z r := by
  have hemb : MeasurableEmbedding (sphereIsometryMap (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))) := by
    apply Measurable.measurableEmbedding
      (sphereIsometryMap_measurable _) _
    intro u v huv
    apply Subtype.ext
    have := congrArg Subtype.val huv
    simpa [sphereIsometryMap] using this
  have h := (unitSphereLaw_isometry_preserving (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))).integral_comp hemb
    (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (r * inner ℝ z (u:Spin (n+1))))
  simpa [sphericalExp,sphereIsometryMap] using h

lemma sphericalExp_eq_cosh (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z r =
      ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.cosh (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1) := by
  have hi (s : ℝ) : Integrable (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (s * inner ℝ z (u:Spin (n+1)))) (unitSphereLaw (n+1)) :=
    unitSphere_continuous_integrable (by fun_prop)
  simp only [Real.cosh_eq,integral_div]
  rw [integral_add (hi r) (by simpa only [neg_mul] using hi (-r))]
  simp only [← neg_mul]
  change sphericalExp n z r = (sphericalExp n z r + sphericalExp n z (-r))/2
  rw [sphericalExp_even]
  ring

lemma sphericalExp_mono (n : ℕ) (z : Spin (n+1)) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : sphericalExp n z r ≤ sphericalExp n z s := by
  rw [sphericalExp_eq_cosh,sphericalExp_eq_cosh]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

lemma one_le_sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    1 ≤ sphericalExp n z r := by
  rw [sphericalExp_eq_cosh]
  calc
    (1:ℝ) = ∫ _ : Metric.sphere (0:Spin (n+1)) 1, (1:ℝ) ∂unitSphereLaw (n+1) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (unitSphere_continuous_integrable (by fun_prop)) (fun u => Real.one_le_cosh _)

end SphericalPerceptron
end
end
end

end OAI
