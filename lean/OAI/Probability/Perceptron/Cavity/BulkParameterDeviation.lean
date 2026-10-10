import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkEnergyDeviation
import OAI.Probability.Perceptron.Variational.ParameterResampling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeature_joint_continuous (N : ℕ) :
    Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N => bulkFeature N a.1 a.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => fun_prop
  | inr i =>
    change Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N =>
      bulkAmplitude N a.1 i.1*spinTensorFeature N (bulkDegree i.1) a.2 i.2)
    apply Continuous.mul
    · unfold bulkAmplitude; fun_prop
    · exact ((EuclideanSpace.proj i.2).continuous.comp (spinTensorFeature_continuous N (bulkDegree i.1))).comp continuous_snd

lemma bulkHamiltonian_parameter_continuous (N M : ℕ) (f : ℝ→ᵇℝ) :
    Continuous (fun a : ((ℕ→ℝ) × BulkDisorder N M) × NormalizedSpin N =>
      bulkHamiltonian N M f a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold bulkHamiltonian
  exact ((normalizedPatternEnergy_continuous N M f).comp
    (continuous_fst.snd.fst.prodMk continuous_snd)).add
    (((bulkFeature_joint_continuous N).comp (continuous_fst.fst.prodMk continuous_snd)).inner continuous_fst.snd.snd)

def bulkDegreeDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) : ℝ :=
  bulkEnergyDeviation n M f v p (v (p.val+1))

lemma bulkDegreeDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Measurable (bulkDegreeDeviation n M f p) := by
  let H := fun a : (ℕ→ℝ) × BulkDisorder (n+1) M =>
    bulkHamiltonian (n+1) M f a.1 a.2.1 a.2.2
  let Y := fun a : (ℕ→ℝ) × BulkDisorder (n+1) M =>
    fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x
  have hH : Measurable (Function.uncurry H) := (bulkHamiltonian_parameter_continuous (n+1) M f).measurable
  have hY : Measurable (Function.uncurry Y) :=
    ((bulkY_measurable (n+1) p).comp (measurable_fst.snd.snd.prodMk measurable_snd)).const_mul _
  have hE := (measurable_tiltMean_param (unitSphereLaw (n+1)) hH hY).stronglyMeasurable.integral_prod_right'
    (ν:=bulkDisorderLaw (n+1) M)
  have he := (measurable_tiltMean_param (unitSphereLaw (n+1)) hH
    (show Measurable (Function.uncurry (fun a x => |Y a x-∫ b, tiltMean (unitSphereLaw (n+1)) (H (a.1,b)) (Y (a.1,b)) 1 ∂bulkDisorderLaw (n+1) M|)) from
      (hY.sub (hE.measurable.comp measurable_fst.fst)).abs)).stronglyMeasurable.integral_prod_right'
        (ν:=bulkDisorderLaw (n+1) M) |>.measurable
  convert he using 1
  funext v
  unfold bulkDegreeDeviation bulkEnergyDeviation
  simp_rw [bulkCouplingSlope_eq_mean,Function.update_eq_self]
  rfl

lemma bulkDegreeDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) :
    0≤bulkDegreeDeviation n M f p v := bulkEnergyDeviation_nonneg n M f v p _

lemma bulkDegreeDeviation_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Integrable (bulkDegreeDeviation n M f p) bulkParameterLaw := by
  apply Integrable.of_bound (bulkDegreeDeviation_measurable n M f p).aestronglyMeasurable
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (bulkDegreeDeviation_nonneg n M f p v)]
    exact bulkEnergyDeviation_bound n M f v p _

lemma bulkDegreeDeviation_update (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) (u : ℝ) :
    bulkDegreeDeviation n M f p (Function.update v (p.val+1) u)=bulkEnergyDeviation n M f v p u := by
  simp only [bulkDegreeDeviation,Function.update_self,bulkEnergyDeviation,bulkCouplingSlope,Function.update_idem]

lemma bulkDegreeDeviation_integral_bound (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1))
    {s : ℝ} (hs : 0<s) (hs1 : s≤1) :
    (∫ v, bulkDegreeDeviation n M f p v ∂bulkParameterLaw)≤
      Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  rw [bulkParameterLaw_integral_resample (p.val+1) (bulkDegreeDeviation_integrable n M f p)]
  simp only [bulkDegreeDeviation_update]
  calc
    _ ≤ ∫ _ : ℕ→ℝ, Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s ∂bulkParameterLaw := by
      apply integral_mono_of_nonneg (ae_of_all _ fun v => intervalIntegral.integral_nonneg (by norm_num)
        (fun u _ => bulkEnergyDeviation_nonneg n M f v p u)) (integrable_const _)
      filter_upwards [bulkParameterLaw_ae] with v hv
      exact bulkEnergyDeviation_integrated_bound n M f v p hs hs1 (by norm_num) (fun j =>
        abs_le.mpr ⟨by linarith [(hv j).1],by linarith [(hv j).2]⟩)
    _ = _ := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
