import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereBridge
import OAI.Probability.Perceptron.Sphere.SphereHeat

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma canonicalRadial_exp_integrable (n : ℕ) (z : Spin (n+1)) :
    Integrable (fun x => Real.exp (inner ℝ z x)) (canonicalRadialMass n 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
  rw [canonicalRadial_linear_integral n (by norm_num)]
  exact ENNReal.ofReal_ne_top

lemma canonicalRadial_exp_integral (n : ℕ) (z : Spin (n+1)) :
    (∫ x, Real.exp (inner ℝ z x) ∂canonicalRadialMass n 1)=Real.exp (‖z‖^2/2) := by
  have h := canonicalRadial_linear_integral n (b:=1) (by norm_num) z
  rw [←ofReal_integral_eq_lintegral_ofReal (canonicalRadial_exp_integrable n z)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)] at h
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => (Real.exp_pos _).le) (Real.exp_pos _).le).mp
  simpa using h

lemma canonicalRadialMass_eq_stdGaussian (n : ℕ) :
    canonicalRadialMass n 1=stdGaussian (Spin (n+1)) := by
  apply Measure.ext_of_charFun
  funext z
  have hm : mgf (fun x => inner ℝ z x) (canonicalRadialMass n 1)=
      mgf (fun x => inner ℝ z x) (stdGaussian (Spin (n+1))) := by
    funext t
    change (∫ x, Real.exp (t*inner ℝ z x) ∂canonicalRadialMass n 1)=
      (∫ x, Real.exp (t*inner ℝ z x) ∂stdGaussian (Spin (n+1)))
    rw [integral_exp_inner_stdGaussian]
    have h := canonicalRadial_exp_integral n (t • z)
    simp only [real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
    exact h
  have hs : integrableExpSet (fun x => inner ℝ z x) (canonicalRadialMass n 1)=univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t*inner ℝ z x)) _
    simpa only [real_inner_smul_left] using canonicalRadial_exp_integrable n (t • z)
  have h := eqOn_complexMGF_of_mgf hm (show (Complex.I:ℂ)∈{w | w.re∈interior
    (integrableExpSet (fun x => inner ℝ z x) (canonicalRadialMass n 1))} by simp [hs])
  simpa only [complexMGF,charFun_apply,real_inner_comm z, mul_comm Complex.I] using h

def gaussianRadialWeight (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (radialNormalizer n * Real.exp (-(1/2:ℝ)*r^2))

def gaussianRadiusLaw (n : ℕ) : Measure (Ioi (0:ℝ)) :=
  (haarRadiusMeasure (volume : Measure (Spin (n+1)))).withDensity
    (fun r => gaussianRadialWeight n r)

lemma stdGaussian_polar_lintegral (n : ℕ) (f : Spin (n+1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂stdGaussian (Spin (n+1)))=
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
        f (r.val • u.val) ∂unitSphereLaw (n+1) ∂gaussianRadiusLaw n := by
  rw [←canonicalRadialMass_eq_stdGaussian,canonicalRadialMass,
    lintegral_withDensity_eq_lintegral_mul _
      (canonicalRadialDensity_continuous n 1).measurable.ennreal_ofReal hf]
  change (∫⁻ x, gaussianRadialWeight n ‖x‖ * f x)=_
  rw [polar_weighted_lintegral volume f hf (gaussianRadialWeight n) (by unfold gaussianRadialWeight; fun_prop)]
  rw [gaussianRadiusLaw,lintegral_withDensity_eq_lintegral_mul _ (by unfold gaussianRadialWeight; fun_prop)]
  · rfl
  · exact Measurable.lintegral_prod_right (hf.comp (measurable_fst.subtype_val.smul measurable_snd.subtype_val))

instance gaussianRadiusLaw_probability (n : ℕ) : IsProbabilityMeasure (gaussianRadiusLaw n) := by
  constructor
  have h := stdGaussian_polar_lintegral n (fun _ => 1) measurable_const
  simpa using h.symm

lemma normalizedGaussian_smul (n : ℕ) (r : Ioi (0:ℝ))
    (u : Metric.sphere (0:Spin (n+1)) 1) :
    ‖r.val • u.val‖⁻¹ • (r.val • u.val)=u.val := by
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one,smul_smul,
    inv_mul_cancel₀ (ne_of_gt r.prop),one_smul]

lemma normalizedGaussian_polar_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => (‖x‖,‖x‖⁻¹ • x))=
      ((gaussianRadiusLaw n).map Subtype.val).prod
        ((unitSphereLaw (n+1)).map Subtype.val) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop)]
  rw [stdGaussian_polar_lintegral n (fun x => F (‖x‖,‖x‖⁻¹ • x)) (by fun_prop),
    lintegral_prod _ hF.aemeasurable]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro r
  rw [lintegral_map (f:=fun y : Spin (n+1) => F (r.val,y)) (by fun_prop) measurable_subtype_coe]
  apply lintegral_congr
  intro u
  rw [normalizedGaussian_smul]
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one]

end SphericalPerceptronFreeEnergy
end

end OAI
