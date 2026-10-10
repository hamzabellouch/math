import Mathlib
import OAI.Geometry.PrescribedPotential.ChartParametrix
import OAI.Geometry.PrescribedPotential.ParameterLocal
import OAI.Geometry.PrescribedPotential.SobolevLocalization

namespace OAI

/-! Parametrix Commutator. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Real

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weak_second_product (v w : E) (g : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (∂_{w} (smulLeftCLM ℂ g u)) =
      smulLeftCLM ℂ g (∂_{v} (∂_{w} u)) +
        (smulLeftCLM ℂ (⇑(∂_{v} g : 𝓢(E, ℂ))) (∂_{w} u) +
          smulLeftCLM ℂ (⇑(∂_{w} g : 𝓢(E, ℂ))) (∂_{v} u) +
            smulLeftCLM ℂ (⇑(∂_{v} (∂_{w} g) : 𝓢(E, ℂ))) u) := by
  rw [weak_deriv_product, lineDerivOp_add, weak_deriv_product, weak_deriv_product]
  abel

end SobolevChart

namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
variable {n : ℕ}

 

def cutoffError (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (g : 𝓢(EC n, ℂ)) (u : L2 (EC n)) (Du : BasisIndex n → L2 (EC n)) : L2 (EC n) :=
  ∑ k, ∑ l, multiply (c k l)
    (multiply (∂_{stdOrthonormalBasis ℝ (EC n) k} g).toBoundedContinuousFunction (Du l) +
     multiply (∂_{stdOrthonormalBasis ℝ (EC n) l} g).toBoundedContinuousFunction (Du k) +
     multiply (∂_{stdOrthonormalBasis ℝ (EC n) k}
       (∂_{stdOrthonormalBasis ℝ (EC n) l} g)).toBoundedContinuousFunction u)

lemma cutoffError_distribution
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth)
    (g : 𝓢(EC n, ℂ)) (u : L2 (EC n)) (Du : BasisIndex n → L2 (EC n))
    (hDu : ∀ k, (Du k : 𝓢'(EC n, ℂ)) = ∂_{stdOrthonormalBasis ℝ (EC n) k} (u : 𝓢'(EC n, ℂ))) :
    (cutoffError c g u Du : 𝓢'(EC n, ℂ)) =
      chartDifferential c (smulLeftCLM ℂ g (u : 𝓢'(EC n, ℂ))) -
        smulLeftCLM ℂ g (chartDifferential c (u : 𝓢'(EC n, ℂ))) := by
  classical
  change Lp.toTemperedDistributionCLM ℂ volume 2 (cutoffError c g u Du) = _
  simp only [cutoffError, map_sum, chartDifferential,
    _root_.sum_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    Lp.toTemperedDistributionCLM_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [multiply_distribution _ (hc k l)]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_add]
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [multiply_distribution _ (∂_{stdOrthonormalBasis ℝ (EC n) k} g).hasTemperateGrowth,
    multiply_distribution _ (∂_{stdOrthonormalBasis ℝ (EC n) l} g).hasTemperateGrowth,
    multiply_distribution _ (∂_{stdOrthonormalBasis ℝ (EC n) k}
      (∂_{stdOrthonormalBasis ℝ (EC n) l} g)).hasTemperateGrowth,
    hDu, hDu, SobolevChart.weak_second_product]
  simp only [map_add]
  have he : smulLeftCLM ℂ (c k l) (smulLeftCLM ℂ g
      (∂_{stdOrthonormalBasis ℝ (EC n) k}
        (∂_{stdOrthonormalBasis ℝ (EC n) l} (u : 𝓢'(EC n, ℂ))))) =
      smulLeftCLM ℂ g (smulLeftCLM ℂ (c k l)
        (∂_{stdOrthonormalBasis ℝ (EC n) k}
          (∂_{stdOrthonormalBasis ℝ (EC n) l} (u : 𝓢'(EC n, ℂ))))) := by
    rw [smulLeftCLM_smulLeftCLM_apply g.hasTemperateGrowth (hc k l),
      smulLeftCLM_smulLeftCLM_apply (hc k l) g.hasTemperateGrowth]
    congr 2
    ext x
    exact mul_comm _ _
  rw [he]
  abel

lemma cutoffError_bound
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (g : 𝓢(EC n, ℂ)) (u : L2 (EC n)) (Du : BasisIndex n → L2 (EC n)) :
    ‖cutoffError c g u Du‖ ≤ ∑ k, ∑ l, ‖c k l‖ *
      (‖(∂_{stdOrthonormalBasis ℝ (EC n) k} g).toBoundedContinuousFunction‖ * ‖Du l‖ +
       ‖(∂_{stdOrthonormalBasis ℝ (EC n) l} g).toBoundedContinuousFunction‖ * ‖Du k‖ +
       ‖(∂_{stdOrthonormalBasis ℝ (EC n) k}
          (∂_{stdOrthonormalBasis ℝ (EC n) l} g)).toBoundedContinuousFunction‖ * ‖u‖) := by
  classical
  unfold cutoffError
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  apply (multiply_norm_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_add_le _ _).trans (add_le_add (multiply_norm_le _ _) (multiply_norm_le _ _))
  · exact multiply_norm_le _ _

 

def parameterCutoffError (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hsmall : perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH < 1)
    (g : 𝓢(EC n, ℂ)) (f : L2 (EC n)) : L2 (EC n) :=
  cutoffError (extendedCoefficient H a) g
    (parameterLocalZero H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall f)
    (fun k => parameterLocalFirst H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall
      (stdOrthonormalBasis ℝ (EC n) k) f)

lemma parameterCutoffError_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (ha : ∀ k l, (a k l : EC n → ℂ).HasTemperateGrowth)
    (hsmall : perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH < 1)
    (g : 𝓢(EC n, ℂ)) (f : L2 (EC n)) :
    let u := realize 2 (parameterLocal H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall f)
    (parameterCutoffError H hH m hm a hsmall g f : 𝓢'(EC n, ℂ)) =
      chartDifferential (extendedCoefficient H a) (smulLeftCLM ℂ g u) -
        smulLeftCLM ℂ g (chartDifferential (extendedCoefficient H a) u) := by
  have hDu : ∀ k,
      (parameterLocalFirst H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall
        (stdOrthonormalBasis ℝ (EC n) k) f : 𝓢'(EC n, ℂ)) =
      ∂_{stdOrthonormalBasis ℝ (EC n) k}
        (parameterLocalZero H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall f : 𝓢'(EC n, ℂ)) := by
    intro k
    rw [parameterLocalFirst_distribution, parameterLocalZero_distribution]
  simpa only [parameterCutoffError, parameterLocalZero_distribution] using
    cutoffError_distribution (extendedCoefficient H a) (extendedCoefficient_temperate H a ha)
      g _ _ hDu

 
def cutoffErrorConstant (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ) (g : 𝓢(EC n, ℂ)) : ℝ :=
  (∑ k, ∑ l, ‖extendedCoefficient H a k l‖ *
    (‖(∂_{stdOrthonormalBasis ℝ (EC n) k} g).toBoundedContinuousFunction‖ *
        (2 * Real.pi * ‖stdOrthonormalBasis ℝ (EC n) l‖ * ellipticBound H hH) +
     ‖(∂_{stdOrthonormalBasis ℝ (EC n) l} g).toBoundedContinuousFunction‖ *
        (2 * Real.pi * ‖stdOrthonormalBasis ℝ (EC n) k‖ * ellipticBound H hH) +
     ‖(∂_{stdOrthonormalBasis ℝ (EC n) k}
        (∂_{stdOrthonormalBasis ℝ (EC n) l} g)).toBoundedContinuousFunction‖)) /
    (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH)

lemma parameterCutoffError_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hsmall : perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH < 1)
    (g : 𝓢(EC n, ℂ)) (f : L2 (EC n)) :
    ‖parameterCutoffError H hH m hm a hsmall g f‖ ≤
      (cutoffErrorConstant H hH a g / m) * ‖f‖ := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hden : 0 < 1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH :=
    sub_pos.mpr hsmall
  have hz : ‖parameterLocalZero H hH m hm (stdOrthonormalBasis ℝ (EC n)) a hsmall f‖ ≤
      (1 / (m * (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH))) * ‖f‖ := by
    apply (parameterLocalZero_bound H hH m hm _ a hsmall f).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hi : (m^2)⁻¹ ≤ m⁻¹ := inv_anti₀ hm0 (by nlinarith)
    calc
      _ ≤ m⁻¹ / (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH) :=
        div_le_div_of_nonneg_right hi hden.le
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring
  apply (cutoffError_bound (extendedCoefficient H a) g _ _).trans
  unfold cutoffErrorConstant
  simp only [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  calc
    _ ≤ ‖extendedCoefficient H a k l‖ *
        (‖(∂_{stdOrthonormalBasis ℝ (EC n) k} g).toBoundedContinuousFunction‖ *
            (((2 * Real.pi * ‖stdOrthonormalBasis ℝ (EC n) l‖ * ellipticBound H hH) /
              (m * (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH))) * ‖f‖) +
         ‖(∂_{stdOrthonormalBasis ℝ (EC n) l} g).toBoundedContinuousFunction‖ *
            (((2 * Real.pi * ‖stdOrthonormalBasis ℝ (EC n) k‖ * ellipticBound H hH) /
              (m * (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH))) * ‖f‖) +
         ‖(∂_{stdOrthonormalBasis ℝ (EC n) k}
            (∂_{stdOrthonormalBasis ℝ (EC n) l} g)).toBoundedContinuousFunction‖ *
            ((1 / (m * (1 - perturbationBound (stdOrthonormalBasis ℝ (EC n)) a * ellipticBound H hH))) * ‖f‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (parameterLocalFirst_bound H hH m hm _ a hsmall _ f)
            (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left (parameterLocalFirst_bound H hH m hm _ a hsmall _ f)
            (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end MetricLocalization

end
end

end OAI
