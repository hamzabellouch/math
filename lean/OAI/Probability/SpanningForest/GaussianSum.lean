import OAI.Probability.SpanningForest.GaussianMomentScaling

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {Q : ι → Ω → ℝ} {v : ι → ℝ≥0}

theorem independent_centered_gaussian_sum_hasLaw
    (hQ : ∀ i, HasLaw (Q i) (gaussianReal 0 (v i)) P) (hind : iIndepFun Q P) :
    HasLaw (fun ω => ∑ i, Q i ω) (gaussianReal 0 (∑ i, v i)) P := by
  have hG : HasGaussianLaw (fun ω => ∑ i, Q i ω) P :=
    iIndepFun.hasGaussianLaw_fun_sum (fun i => (hQ i).hasGaussianLaw) hind
  have hmean : (∫ ω, ∑ i, Q i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hQ i).hasGaussianLaw.integrable)]
    simp only [fun i => (hQ i).integral_eq, integral_id_gaussianReal, Finset.sum_const_zero]
  have hvar : Var[fun ω => ∑ i, Q i ω; P] = ∑ i, (v i : ℝ) := by
    have h := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ => (hQ i).hasGaussianLaw.memLp_two)
      (fun i _ j _ hij => hind.indepFun hij)
    have heq : (fun ω => ∑ i, Q i ω) = ∑ i, Q i := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    simpa only [fun i => (hQ i).variance_eq, variance_id_gaussianReal] using h
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean, hvar]
  congr 1
  simp only [← NNReal.coe_sum, Real.toNNReal_coe]

theorem independent_weighted_gaussian_sum_hasLaw
    (hQ : ∀ i, HasLaw (Q i) (gaussianReal 0 (v i)) P)
    (hind : iIndepFun Q P) (θ : ι → ℝ) :
    HasLaw (fun ω => ∑ i, θ i * Q i ω)
      (gaussianReal 0 (∑ i, NNReal.mk ((θ i) ^ 2) (sq_nonneg _) * v i)) P := by
  apply independent_centered_gaussian_sum_hasLaw
  · intro i
    simpa only [mul_zero] using gaussianReal_const_mul (hQ i) (θ i)
  · exact hind.comp (fun i z => θ i * z) (by fun_prop)

end Problem336

end

end OAI
