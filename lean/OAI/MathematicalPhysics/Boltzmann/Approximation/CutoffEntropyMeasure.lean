import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveComparisonBound

namespace OAI

/-! # The extended nonnegative cutoff dissipation agrees with positive production -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def cutoffExtendedProduction (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ≥0∞ :=
  if ‖z.1.2.1-z.1.2.2‖ < b then
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*
      extendedEntropyProduction
        (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  else 0

omit [MeasurableSpace X] in
theorem positiveCutoffProduction_formula (b : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ z, 0 < f z) (z : (X × (Velocity × Velocity)) × Sphere) :
    positiveCutoffProduction b f z =
      if ‖z.1.2.1-z.1.2.2‖ < b then
        (1/4:ℝ)*collisionKernel z.1.2.1 z.1.2.2 z.2*
          ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
            f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))*
          Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/
            (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))))
      else 0 := by
  unfold positiveCutoffProduction
  rw [collisionJump_log_relative f hf,collisionJump_log_density f hf]
  simp only [truncatedPreRate,truncatedPostRate,Set.indicator_apply,Set.mem_ofPred_eq]
  by_cases hc : ‖z.1.2.1-z.1.2.2‖ < b
  · simp only [hc,↓reduceIte,postRate_formula,preRate]
    ring
  · simp only [hc,↓reduceIte,sub_self,mul_zero]

omit [MeasurableSpace X] in
theorem ofReal_positiveCutoffProduction (b : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ z, 0 < f z) (z : (X × (Velocity × Velocity)) × Sphere) :
    ENNReal.ofReal (positiveCutoffProduction b f z) = (4:ℝ≥0∞)⁻¹*cutoffExtendedProduction b f z := by
  rw [positiveCutoffProduction_formula b f hf]
  have hA := mul_pos (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hB := mul_pos (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
  by_cases hc : ‖z.1.2.1-z.1.2.2‖ < b
  · simp only [cutoffExtendedProduction,hc,↓reduceIte]
    have he : extendedEntropyProduction
        (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)) =
        ENNReal.ofReal ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
          f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))*
          Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/
            (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)))) := by
      simp [extendedEntropyProduction,hA,hB,hA.ne',hB.ne']
    rw [he]
    rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (collisionKernel_nonneg _ _ _)),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
    norm_num [mul_assoc]
  · simp [hc,cutoffExtendedProduction]

def cutoffExtendedDissipation (μ : Measure X) (b : ℝ) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, cutoffExtendedProduction b f z
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

theorem ofReal_integral_positiveCutoffProduction {μ : Measure X} (b : ℝ)
    (f : X × Velocity → ℝ) (hf : ∀ z, 0 < f z)
    (hi : Integrable (positiveCutoffProduction b f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    ENNReal.ofReal (∫ z, positiveCutoffProduction b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      cutoffExtendedDissipation μ b f := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (positiveCutoffProduction_nonneg b f hf))]
  simp_rw [ofReal_positiveCutoffProduction b f hf]
  exact lintegral_const_mul' _ _ (by norm_num)

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
