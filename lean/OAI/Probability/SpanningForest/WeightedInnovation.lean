import OAI.Probability.SpanningForest.InnovationMoments
import OAI.Probability.SpanningForest.InnovationTaylor
import OAI.Probability.SpanningForest.GaussianMomentScaling

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem336.Innovation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem weighted_square_perturbation [IsFiniteMeasure P]
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a : ℝ}
    (hQ : Integrable Q P) (hQ2 : Integrable (fun ω => Q ω ^ 2) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1) :
    ‖(∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 ∂P) -
        ∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P‖ ≤
      2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2 * P.real Set.univ := by
  have hD2 := InnovationMoments.integrable_square_add_of_bounded
    hQ.aestronglyMeasurable hR hQ2 ha hRbound
  have hCD2 : Integrable (fun ω => ((Q ω + R ω : ℝ) : ℂ) ^ 2) P := by
    convert Complex.ofRealCLM.integrable_comp hD2 using 1
    ext ω
    simp
  have hCQ2 : Integrable (fun ω => (Q ω : ℂ) ^ 2) P := by
    convert Complex.ofRealCLM.integrable_comp hQ2 using 1
    ext ω
    simp
  have hKD2 := hCD2.bdd_mul hKmeas hK
  have hKQ2 := hCQ2.bdd_mul hKmeas hK
  have hbound : Integrable (fun ω => 2 * a * |Q ω| + a ^ 2) P :=
    (hQ.abs.const_mul (2 * a)).add (integrable_const _)
  rw [← integral_sub hKD2 hKQ2]
  calc
    _ ≤ ∫ ω, 2 * a * |Q ω| + a ^ 2 ∂P := by
      apply norm_integral_le_of_norm_le hbound
      filter_upwards [hRbound, hK] with ω hRω hKω
      have heq : K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 - K ω * (Q ω : ℂ) ^ 2 =
          K ω * ((((Q ω + R ω) ^ 2 - Q ω ^ 2 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ 1 * |(Q ω + R ω) ^ 2 - Q ω ^ 2| :=
          mul_le_mul_of_nonneg_right hKω (abs_nonneg _)
        _ ≤ 2 * a * |Q ω| + a ^ 2 := by
          simpa only [one_mul] using
            InnovationMoments.abs_square_perturbation_le (Q ω) (R ω) a ha hRω
    _ = _ := by
      rw [integral_add (hQ.abs.const_mul _) (integrable_const _),
        integral_const_mul, integral_const]
      simp only [smul_eq_mul]
      ring

theorem weighted_bounded_perturbation_characteristic [IsProbabilityMeasure P]
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a q : ℝ}
    (hQ : Integrable Q P) (hQ2 : Integrable (fun ω => Q ω ^ 2) P)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hQmoment : (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (2 * q : ℝ) * (∫ ω, K ω ∂P)) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-q) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      16 * ((∫ ω, |Q ω| ^ 3 ∂P) + a ^ 3) +
        (2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2) / 2 + q ^ 2 := by
  have hRint : Integrable R P := Integrable.of_bound hR a (by simpa using hRbound)
  have hD2 := InnovationMoments.integrable_square_add_of_bounded
    hQ.aestronglyMeasurable hR hQ2 ha hRbound
  have hD3 := InnovationMoments.integrable_abs_cube_add_of_bounded
    hQ.aestronglyMeasurable hR hQ3 ha hRbound
  have hM : ‖(∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 ∂P) -
      (2 * q : ℝ) * (∫ ω, K ω ∂P)‖ ≤
      2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2 := by
    rw [← hQmoment]
    simpa using weighted_square_perturbation hQ hQ2 hR ha hRbound hKmeas hK
  have hstep := weighted_characteristic_gaussian_bound P (fun ω => Q ω + R ω) K
    hKmeas hK (hQ.add hRint) hD2 hD3 hmean hq0 hq1 hM
  have hthird : (∫ ω, |Q ω + R ω| ^ 3 ∂P) ≤
      4 * ((∫ ω, |Q ω| ^ 3 ∂P) + a ^ 3) := by
    simpa using InnovationMoments.integral_abs_cube_perturbation_le
      hQ.aestronglyMeasurable hR hQ3 ha hRbound
  linarith

theorem gaussian_bounded_perturbation_characteristic
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a : ℝ} {v : ℝ≥0}
    (hLaw : ProbabilityTheory.HasLaw Q (ProbabilityTheory.gaussianReal 0 v) P)
    (hIndep : ProbabilityTheory.IndepFun K Q P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0)
    (hv : (v : ℝ) ≤ 2) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-((v : ℝ) / 2)) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      16 * ((Real.sqrt (v : ℝ)) ^ 3 *
        (∫ z : ℝ, |z| ^ 3 ∂ProbabilityTheory.gaussianReal 0 1) + a ^ 3) +
        (2 * a * Real.sqrt (v : ℝ) + a ^ 2) / 2 + ((v : ℝ) / 2) ^ 2 := by
  let : IsProbabilityMeasure P := hLaw.isProbabilityMeasure
  have hQ : Integrable Q P := hLaw.hasGaussianLaw.integrable
  have hQ2 : Integrable (fun ω => Q ω ^ 2) P := by
    simpa only [sq_abs] using gaussian_hasLaw_integrable_abs_pow hLaw 2
  have hQ3 := gaussian_hasLaw_integrable_abs_pow hLaw 3
  have hQmoment : (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (2 * ((v : ℝ) / 2) : ℝ) * (∫ ω, K ω ∂P) := by
    rw [gaussian_independent_weighted_second_moment hLaw hKmeas.aemeasurable hIndep]
    push_cast
    ring
  have hq0 : 0 ≤ (v : ℝ) / 2 := by positivity
  have hq1 : (v : ℝ) / 2 ≤ 1 := by linarith
  have hstep := weighted_bounded_perturbation_characteristic hQ hQ2 hQ3 hR ha
    hRbound hKmeas hK hmean hq0 hq1 hQmoment
  apply hstep.trans
  rw [gaussian_hasLaw_absolute_moment hLaw 3]
  gcongr
  exact gaussian_hasLaw_absolute_first_moment_le hLaw

end Problem336.Innovation

end

end OAI
