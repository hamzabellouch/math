import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Ising.ConditionalCopyBounds

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem abs_artanh_le_two_mul_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.artanh x| ≤ 2 * |x| := by
  have hd (z : ℝ) (hz : z ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivWithinAt Real.artanh (1 / (1 - z ^ 2)) (Icc (-1 / 2) (1 / 2)) z :=
    (hasDerivAt_artanh_interval (by constructor <;> linarith [hz.1, hz.2])).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      ‖1 / (1 - z ^ 2)‖ ≤ (2 : ℝ) := by
    have hsq : z ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg (by linarith [hz.1] : 0 ≤ z + 1 / 2)
        (by linarith [hz.2] : 0 ≤ 1 / 2 - z)]
    have hden : 0 < 1 - z ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (1 - z ^ 2))]
    exact (div_le_iff₀ hden).mpr (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
    (by norm_num : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (show x ∈ Icc (-1 / 2 : ℝ) (1 / 2) by
      constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2])
  simpa only [Real.artanh_zero, sub_zero, Real.norm_eq_abs] using h

theorem artanh_sub_sq_le_information {x y K : ℝ}
    (hK : |Real.artanh x - Real.artanh y| ≤ K) :
    (Real.artanh x - Real.artanh y) ^ 2 ≤ (8 + 4 * K ^ 2) * (x ^ 2 + y ^ 2) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hK
  have hdiff : (Real.artanh x - Real.artanh y) ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hK 2)
  by_cases hx : |x| ≤ 1 / 2
  · by_cases hy : |y| ≤ 1 / 2
    · have hax : (Real.artanh x) ^ 2 ≤ 4 * x ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) (abs_artanh_le_two_mul_of_abs_le_half hx)
        nlinarith only [h, sq_abs (Real.artanh x), sq_abs x]
      have hay : (Real.artanh y) ^ 2 ≤ 4 * y ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) (abs_artanh_le_two_mul_of_abs_le_half hy)
        nlinarith only [h, sq_abs (Real.artanh y), sq_abs y]
      have hsum : 0 ≤ 4 * K ^ 2 * (x ^ 2 + y ^ 2) := by positivity
      nlinarith [sq_nonneg (Real.artanh x + Real.artanh y)]
    · have hy' : 1 / 2 ≤ |y| := (lt_of_not_ge hy).le
      have hy2 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hy'
      have hmul := mul_le_mul_of_nonneg_left hy2 (sq_nonneg K)
      nlinarith [sq_abs y, sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg K) (sq_nonneg x)]
  · have hx' : 1 / 2 ≤ |x| := (lt_of_not_ge hx).le
    have hx2 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hx'
    have hmul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg K)
    nlinarith [sq_abs x, sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg K) (sq_nonneg y)]

namespace IsingConditionalCopyBounds

open IsingObservationInnovation

def posteriorInformation {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    (v : TreeVertex d) (t : ℝ≥0) : ℝ :=
  ∫ x, (IsingObservationInnovation.posterior beta v t x) ^ 2 ∂observationLaw μ

theorem posteriorInformation_eq_gaussian
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v : TreeVertex d) :
    posteriorInformation beta μ v t =
      ∫ p, (PlantedSymmetry.posteriorMagnetization (μ.prod (PlantedSymmetry.gaussianNoiseLaw
        (TreeVertex d) t)) t v p) ^ 2 ∂μ.prod
          (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (PlantedSymmetry.observation t)
      ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)).map
        (PlantedSymmetry.observation t))
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(PlantedSymmetry.measurable_observation t).aemeasurable, rfl⟩
  have hsame := (heval.identDistrib hobs).comp
    ((measurable_infiniteGibbsSpinMean beta v).pow_const 2)
  calc
    _ = ∫ p, (infiniteGibbsSpinMean beta v (PlantedSymmetry.observation t p)) ^ 2
        ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := hsame.integral_eq
    _ = _ := integral_congr_ae
      ((hμ.infiniteGibbsSpinMean_eq_posterior t v).fun_comp (fun z : ℝ => z ^ 2))

theorem fieldDifference_secondMoment_le_information
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
    {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
      2 * (8 + 4 * (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        posteriorInformation beta μ v t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let : IsProbabilityMeasure (observationLaw μ) := by
    unfold observationLaw
    infer_instance
  let m : Paths d → ℝ := IsingObservationInnovation.posterior beta v t
  let C : ℝ := 8 + 4 * (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2
  have hm : Measurable m :=
    (((posterior_progressive beta v).stronglyAdapted t).mono ((filtration d).le t)).measurable
  have hmLp : MemLp m 2 (observationLaw μ) :=
    MemLp.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => posterior_norm_le_one beta v t x))
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have hml := hmLp.comp_measurePreserving hl
  have hmr := hmLp.comp_measurePreserving hr
  have hdiff := (fieldDifference_secondMoment_bounds hμ hbeta hjoint t v).1
  have hlint := hl.hasLaw.integral_comp (f := fun x => (m x) ^ 2)
    (hm.pow_const 2).aestronglyMeasurable
  have hrint := hr.hasLaw.integral_comp (f := fun x => (m x) ^ 2)
    (hm.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at hlint hrint
  calc
    (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
        ∫ q : CopySpace d, C * ((m q.2.1) ^ 2 + (m q.2.2) ^ 2)
          ∂rho ⊗ₘ (eta ×ₖ eta) := by
      apply integral_mono_ae hdiff.integrable_sq
        ((hml.integrable_sq.add hmr.integrable_sq).const_mul C)
      filter_upwards [ae_fieldDifference_bound hμ hbeta hjoint t v] with q hq
      exact artanh_sub_sq_le_information hq
    _ = C * ((∫ q : CopySpace d, (m q.2.1) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) +
          ∫ q : CopySpace d, (m q.2.2) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) := by
      rw [integral_const_mul]
      congr 1
      exact integral_add hml.integrable_sq hmr.integrable_sq
    _ = 2 * (8 + 4 * (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        posteriorInformation beta μ v t := by
      rw [hlint, hrint]
      change C * (posteriorInformation beta μ v t + posteriorInformation beta μ v t) = _
      dsimp [C]
      ring

theorem fieldDifference_secondMoment_le_horizon_information
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
    {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) {T t : ℝ≥0} (ht : t ≤ T)
    (v : TreeVertex d) :
    (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
      2 * (8 + 4 * (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        posteriorInformation beta μ v t := by
  apply (fieldDifference_secondMoment_le_information hμ hbeta hjoint t v).trans
  have hI : 0 ≤ posteriorInformation beta μ v t := integral_nonneg (fun _ => sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ hI
  have htR : (t : ℝ) ≤ (T : ℝ) := ht
  have hK : 0 ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by positivity
  have hsq := pow_le_pow_left₀ hK
    (show 2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta by linarith) 2
  linarith

end IsingConditionalCopyBounds

end Problem367

end

end OAI
