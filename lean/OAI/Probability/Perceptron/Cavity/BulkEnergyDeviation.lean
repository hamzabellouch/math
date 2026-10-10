import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkDeviation
import OAI.Probability.Perceptron.Variational.IntegratedThermal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCouplingSlope_eq_mean (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ)
    (a : BulkDisorder (n+1) M) :
    bulkCouplingSlope n M f v p u a = tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
      (fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x) 1 := by
  rw [tiltMean_const_mul_general]; rfl

lemma bulkCoupledHamiltonian_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f (Function.update v (p.val+1) a.1.1) a.1.2.1 a.1.2.2 a.2) := by
  have hb : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1.2.1 a.1.2.2 a.2) :=
    (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) 0)).comp
      (continuous_fst.snd.prodMk continuous_snd)
  have hy : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkY (n+1) p a.1.2.2 a.2) :=
    ((bulkDirection_continuous (n+1) p).comp continuous_snd).inner continuous_fst.snd.snd
  convert (hb.add (continuous_fst.fst.mul (hy.const_mul (bulkCoefficient (n+1) p)))).measurable using 1
  funext a
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

def bulkEnergyDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) : ℝ :=
  ∫ a, tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
    (fun x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-
      ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M|) 1 ∂bulkDisorderLaw (n+1) M

lemma bulkEnergyDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    0≤bulkEnergyDeviation n M f v p u :=
  integral_nonneg fun _ => tiltMean_nonneg _ (fun _ => abs_nonneg _) _

lemma bulkEnergyDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (bulkEnergyDeviation n M f v p) := by
  have hE := (bulkCouplingSlope_joint_measurable n M f v p).stronglyMeasurable.integral_prod_right'
    (ν:=bulkDisorderLaw (n+1) M)
  have hY : Measurable (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkCoefficient (n+1) p*bulkY (n+1) p a.1.2.2 a.2) :=
    ((bulkY_measurable (n+1) p).comp (measurable_fst.snd.snd.prodMk measurable_snd)).const_mul _
  have hm := kernel_tiltMean_measurable (Kernel.const (ℝ × BulkDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) a.1) a.2.1 a.2.2 x)
    (Y:=fun a x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x-
      ∫ b, bulkCouplingSlope n M f v p a.1 b ∂bulkDisorderLaw (n+1) M|)
    (bulkCoupledHamiltonian_measurable n M f v p) (hY.sub (hE.measurable.comp measurable_fst.fst)).abs
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma bulkEnergyDeviation_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkEnergyDeviation n M f v p u ≤
      2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
  let E := ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M
  have hn := (bulkMarkNorm_memLp n M).integrable (by norm_num)
  have hE : |E|≤bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖ ∂bulkDisorderLaw (n+1) M :=
        integral_mono (bulkExpectedLog_hasDerivAt n M f v p u).1.abs (hn.const_mul _) (bulkCouplingSlope_bound n M f v p u)
      _ = _ := integral_const_mul _ _
  have hb (a : BulkDisorder (n+1) M) :
      tiltMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
        (fun x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-E|) 1 ≤
          bulkCoefficient (n+1) p*‖a.2‖+|E| := by
    have ht := tiltMean_bound_of_integrable (unitSphereLaw (n+1))
      (t:=1) (bulkHamiltonian_section_measurable _ _ _ _ a)
      (((bulkY_measurable _ _).of_uncurry_left.const_mul (bulkCoefficient (n+1) p)).sub_const E).abs
      (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a)
      (fun x => show abs (abs (bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-E))≤bulkCoefficient (n+1) p*‖a.2‖+|E| from by
        rw [abs_abs]
        apply (abs_sub _ _).trans
        rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
        exact add_le_add (mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le) le_rfl)
    exact (le_abs_self _).trans ht
  calc
    _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖+|E| ∂bulkDisorderLaw (n+1) M :=
      integral_mono_of_nonneg (ae_of_all _ fun a => tiltMean_nonneg _ (fun _ => abs_nonneg _) _)
        ((hn.const_mul _).add (integrable_const |E|)) (ae_of_all _ hb)
    _ ≤ _ := by
      rw [integral_add (hn.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
      linarith

lemma bulkEnergyDeviation_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (bulkEnergyDeviation n M f v p) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    (bulkEnergyDeviation_measurable n M f v p).aestronglyMeasurable.restrict
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (bulkEnergyDeviation_nonneg n M f v p u)]
    exact bulkEnergyDeviation_bound n M f v p u

lemma bulkEnergyDeviation_thermal_disorder (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkEnergyDeviation n M f v p u ≤
      Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)+
        bulkSlopeDeviation n M f v p u := by
  have he := annealed_centered_energy_bound (unitSphereLaw (n+1)) (bulkDisorderLaw (n+1) M)
    (H:=fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)
    (Y:=fun a x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) u)).measurable
    ((bulkY_joint_measurable (n+1) M p).const_mul (bulkCoefficient (n+1) p))
    (B:=fun a => bulkCoefficient (n+1) p*‖a.2‖)
    (fun a => by unfold bulkFeatureBound; positivity)
    (fun a => mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg _))
    (bulkHamiltonian_bound (n+1) M f (Function.update v (p.val+1) u))
    (fun a x => by rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]; exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le)
    ((bulkMarkNorm_memLp n M).const_mul _)
  simp_rw [← bulkCouplingSlope_eq_mean] at he
  change bulkEnergyDeviation n M f v p u ≤ _ at he
  apply he.trans_eq
  unfold bulkSlopeDeviation
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    have hh : (fun x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)=
        (fun x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2 x+
          u*(bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)) :=
      funext fun x => bulkHamiltonian_update _ _ _ _ _ _ _ _
    unfold bulkThermalVar thermalVar
    simp only [zero_mul,add_zero,hh]

lemma bulkEnergyDeviation_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    {s C : ℝ} (hs : 0<s) (hs1 : s≤1) (hC : 3≤C) (hv : ∀ j, |v j|≤C) :
    (∫ u in (1:ℝ)..2, bulkEnergyDeviation n M f v p u)≤
      Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  have hsq : IntervalIntegrable (fun u => Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)) volume 1 2 :=
    bulkThermalSqrt_intervalIntegrable n M f v p 1 2
  calc
    _ ≤ ∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)+bulkSlopeDeviation n M f v p u :=
      intervalIntegral.integral_mono (by norm_num) (bulkEnergyDeviation_intervalIntegrable n M f v p 1 2)
        (hsq.add (bulkSlopeDeviation_intervalIntegrable n M f v p 1 2))
        (fun u => bulkEnergyDeviation_thermal_disorder n M f v p u)
    _ = (∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M))+
        ∫ u in (1:ℝ)..2, bulkSlopeDeviation n M f v p u := intervalIntegral.integral_add hsq (bulkSlopeDeviation_intervalIntegrable n M f v p 1 2)
    _ ≤ _ := by have h1 := bulkThermalSqrt_integrated_bound n M f v p; have h2 := bulkSlopeDeviation_integrated_bound n M f v p hs hs1 hC hv; linarith

end SphericalPerceptronFreeEnergy
end

end OAI
