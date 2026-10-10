import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkThermal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCouplingSlope_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) :
    |bulkCouplingSlope n M f v p u a|≤bulkCoefficient (n+1) p*‖a.2‖ := by
  unfold bulkCouplingSlope
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  apply mul_le_mul_of_nonneg_left _ (bulkCoefficient_pos n p).le
  exact tiltMean_bound_of_integrable (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkY_measurable _ _).of_uncurry_left
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a) (bulkY_bound _ _ _)

lemma bulkCouplingSlope_joint_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (Function.uncurry (bulkCouplingSlope n M f v p)) := by
  let H := fun a : ℝ × BulkDisorder (n+1) M => fun x : NormalizedSpin (n+1) =>
    bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.2.1 a.2.2 x+
      a.1*(bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x)
  let Y := fun a : ℝ × BulkDisorder (n+1) M => bulkY (n+1) p a.2.2
  have hYc : Continuous (Function.uncurry Y) :=
    ((bulkDirection_continuous (n+1) p).comp continuous_snd).inner continuous_fst.snd.snd
  have hY : Measurable (Function.uncurry Y) := hYc.measurable
  have hH : Measurable (Function.uncurry H) := by
    have hb : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
        bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1.2.1 a.1.2.2 a.2) :=
      (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) 0)).comp
        (continuous_fst.snd.prodMk continuous_snd)
    exact (hb.add (continuous_fst.fst.mul (hYc.const_mul _))).measurable
  have hm := (kernel_tiltMean_measurable (Kernel.const (ℝ × BulkDisorder (n+1) M) (unitSphereLaw (n+1))) hH hY).const_mul (bulkCoefficient (n+1) p)
  convert hm using 1
  funext a
  unfold Function.uncurry bulkCouplingSlope
  congr 2
  funext x
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

def bulkSlopeDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) : ℝ :=
  ∫ a, |bulkCouplingSlope n M f v p u a-
    ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M| ∂bulkDisorderLaw (n+1) M

lemma bulkSlopeDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (bulkSlopeDeviation n M f v p) := by
  have hd := bulkCouplingSlope_joint_measurable n M f v p
  have hm := (hd.stronglyMeasurable.integral_prod_right' (ν:=bulkDisorderLaw (n+1) M)).measurable
  exact ((hd.sub (hm.comp measurable_fst)).abs).stronglyMeasurable.integral_prod_right'.measurable

lemma bulkSlopeDeviation_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkSlopeDeviation n M f v p u ≤
      2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
  have hi := (bulkExpectedLog_hasDerivAt n M f v p u).1
  have hn := (bulkMarkNorm_memLp n M).integrable (by norm_num)
  have hB : |∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M|≤
      bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
    calc
      _ ≤ ∫ a, |bulkCouplingSlope n M f v p u a| ∂bulkDisorderLaw (n+1) M := abs_integral_le_integral_abs
      _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖ ∂bulkDisorderLaw (n+1) M :=
        integral_mono hi.abs (hn.const_mul _) (bulkCouplingSlope_bound n M f v p u)
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∫ a, bulkCoefficient (n+1) p*‖a.2‖+
        |∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M| ∂bulkDisorderLaw (n+1) M := by
      apply integral_mono (hi.sub (integrable_const _)).abs ((hn.const_mul _).add (integrable_const _))
      intro a
      exact (abs_sub _ _).trans (add_le_add (bulkCouplingSlope_bound n M f v p u a) (le_refl _))
    _ ≤ _ := by
      rw [integral_add (hn.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
      linarith

lemma bulkSlopeDeviation_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (bulkSlopeDeviation n M f v p) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    (bulkSlopeDeviation_measurable n M f v p).aestronglyMeasurable.restrict
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤bulkSlopeDeviation n M f v p u from integral_nonneg fun _ => abs_nonneg _)]
    exact bulkSlopeDeviation_bound n M f v p u

lemma bulkLogPartition_fluctuation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) {C : ℝ}
    (hC : 0≤C) (hv : ∀ p, |v p|≤C) :
    (∫ a : BulkDisorder (n+1) M, |bulkLogPartition n M f v a.1 a.2-bulkExpectedLog n M f v| ∂bulkDisorderLaw (n+1) M) ≤
      Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2) := by
  apply (integral_centered_abs_le_sqrt_variance _ (bulkLogPartition_memLp n M f v)).trans
  apply Real.sqrt_le_sqrt
  apply (bulkLogPartition_variance n M f v).trans
  have hh := mul_le_mul_of_nonneg_left (bulkFeatureBound_sq_le (n+1) v hC (fun j => hv (j+1))) (by positivity : 0≤Real.pi^2/8)
  nlinarith

lemma bulkSlopeDeviation_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    {s C : ℝ} (hs : 0<s) (hs1 : s≤1) (hC : 3≤C) (hv : ∀ p, |v p|≤C) :
    (∫ u in (1:ℝ)..2, bulkSlopeDeviation n M f v p u) ≤
      4*(6*bulkCoefficient (n+1) p^2)*s+
      4*Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  apply integrated_convex_fluctuation_bound (bulkExpectedLog_convex n M f v p)
    (fun u => (bulkExpectedLog_hasDerivAt n M f v p u).2) hs
    (K:=6*bulkCoefficient (n+1) p^2)
  · intro u hu
    calc
      _ ≤ 2*bulkCoefficient (n+1) p^2*|u| := bulk_expected_slope_bound n M f v p u
      _ ≤ _ := by
        have hh : |u|≤3 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
        nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*bulkCoefficient (n+1) p^2)]
  · exact bulkSlopeDeviation_intervalIntegrable n M f v p 1 2
  · intro u hu
    apply integral_convex_derivative_fluctuation (bulkDisorderLaw (n+1) M) hs
      (bulkCouplingSlope_measurable n M f v p u).aestronglyMeasurable
      (ae_of_all _ fun a => ⟨(bulkCoupling_regular n M f v p a).2.1,(bulkCoupling_regular n M f v p a).2.2 u⟩)
      (bulkExpectedLog_convex n M f v p) (fun t => (bulkExpectedLog_hasDerivAt n M f v p t).2)
      (fun t _ => (bulkLogPartition_memLp n M f _).integrable (by norm_num))
    intro t ht
    apply bulkLogPartition_fluctuation n M f _ (by linarith : 0≤C)
    intro j
    by_cases hj : j=p.val+1
    · subst j
      simp only [Function.update_self]
      exact abs_le.mpr ⟨by linarith [ht.1,hu.1],by linarith [ht.2,hu.2]⟩
    · rw [Function.update_of_ne hj]
      exact hv j

end SphericalPerceptronFreeEnergy
end

end OAI
