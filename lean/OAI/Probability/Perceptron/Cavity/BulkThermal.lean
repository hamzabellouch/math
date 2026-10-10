import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkStein

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkMarkNorm_memLp (n M : ℕ) :
    MemLp (fun a : BulkDisorder (n+1) M => ‖a.2‖) 2 (bulkDisorderLaw (n+1) M) := by
  exact ((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).comp_snd
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))

def bulkThermalVar (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : ℝ :=
  thermalVar (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2)
    (fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x) u

lemma bulkThermalVar_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Measurable (bulkThermalVar n M f v p u) :=
  measurable_thermalVar (unitSphereLaw (n+1))
    (bulkHamiltonian_continuous _ _ _ _).measurable
    ((bulkY_joint_measurable _ _ _).const_mul _) u

lemma bulkThermalVar_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : 0≤bulkThermalVar n M f v p u a := by
  apply thermalVar_nonneg (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a)
    ((bulkY_measurable _ _).of_uncurry_left.const_mul _)
    (by unfold bulkFeatureBound; positivity : 0≤(M:ℝ)*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg a.2))
    (bulkHamiltonian_bound _ _ _ _ a)
  intro x
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le

lemma bulkThermalVar_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) :
    |bulkThermalVar n M f v p u a|≤2*(bulkCoefficient (n+1) p*‖a.2‖)^2 := by
  apply thermalVar_bound (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a)
    ((bulkY_measurable _ _).of_uncurry_left.const_mul _)
    (by unfold bulkFeatureBound; positivity : 0≤(M:ℝ)*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg a.2))
    (bulkHamiltonian_bound _ _ _ _ a)
  intro x
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le

lemma bulkThermalVar_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Integrable (bulkThermalVar n M f v p u) (bulkDisorderLaw (n+1) M) := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  apply (((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 2).mono'
    (bulkThermalVar_measurable n M f v p u).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkThermalVar_bound n M f v p u a

lemma bulkExpectedSlope_hasDerivAt (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    HasDerivAt (fun t => ∫ a, bulkCouplingSlope n M f v p t a ∂bulkDisorderLaw (n+1) M)
      (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) u := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  have hd := annealedAffineMean_deriv (unitSphereLaw (n+1)) (bulkDisorderLaw (n+1) M)
    (H := fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2 x)
    (Y := fun a x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)
    (A := fun a => M*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (B := fun a => bulkCoefficient (n+1) p*‖a.2‖)
    (bulkHamiltonian_continuous _ _ _ _).measurable ((bulkY_joint_measurable _ _ _).const_mul _)
    (fun _ => by unfold bulkFeatureBound; positivity) (fun _ => mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg _))
    (bulkHamiltonian_bound _ _ _ _) (fun a x => by
      rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
      exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le)
    (hb.integrable (by norm_num)) ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb) u
  convert hd using 1
  · funext t
    apply integral_congr_ae
    exact ae_of_all _ fun a => by
      unfold bulkCouplingSlope
      rw [← tiltMean_const_mul_general]
      congr 2
      funext x
      exact bulkHamiltonian_update _ _ _ _ _ _ _ _
  · rfl

lemma bulk_expected_slope_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    |∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M|≤
      2*bulkCoefficient (n+1) p^2*|u| := by
  rw [bulk_expected_slope_eq,abs_mul,abs_mul,abs_sq]
  have hh : |∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M|≤1 := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _ : BulkDisorder (n+1) M, (1:ℝ) ∂bulkDisorderLaw (n+1) M := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
        exact ae_of_all _ fun a => gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
          (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkOverlapPower_measurable _ _)
          (bulkHamiltonian_exp_integrable n M f _ a) (bulkOverlapPower_bound _ _)
      _ = 1 := by simp
  have he : |1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M|≤2 := by
    simpa only [abs_one,one_add_one_eq_two] using (abs_sub _ _).trans (add_le_add (le_refl |(1:ℝ)|) hh)
  nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg (bulkCoefficient (n+1) p)) (abs_nonneg u))]

lemma bulkExpectedThermalVar_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) := by
  have he : (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)=
      deriv (fun u => ∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) := by
    funext u
    exact (bulkExpectedSlope_hasDerivAt n M f v p u).deriv.symm
  rw [he]
  exact measurable_deriv _

lemma bulkExpectedThermalVar_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (fun u => ∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M) volume a b := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  have hi := ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 2
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top)
    (bulkExpectedThermalVar_measurable n M f v p).aestronglyMeasurable.restrict
    (∫ x : BulkDisorder (n+1) M, 2*(bulkCoefficient (n+1) p*‖x.2‖)^2 ∂bulkDisorderLaw (n+1) M)
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs]
  exact abs_integral_le_integral_abs.trans (integral_mono (bulkThermalVar_integrable n M f v p u).abs hi
    (bulkThermalVar_bound n M f v p u))

lemma bulkThermalVar_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ u in (1:ℝ)..2, ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) ≤
      6*bulkCoefficient (n+1) p^2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => bulkExpectedSlope_hasDerivAt n M f v p u)
    (bulkExpectedThermalVar_intervalIntegrable n M f v p 1 2)]
  have h1 := bulk_expected_slope_bound n M f v p 1
  have h2 := bulk_expected_slope_bound n M f v p 2
  norm_num only [abs_one,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h1 h2
  linarith [le_abs_self (∫ a, bulkCouplingSlope n M f v p 2 a ∂bulkDisorderLaw (n+1) M),
    neg_abs_le (∫ a, bulkCouplingSlope n M f v p 1 a ∂bulkDisorderLaw (n+1) M)]

end SphericalPerceptronFreeEnergy
end

end OAI
