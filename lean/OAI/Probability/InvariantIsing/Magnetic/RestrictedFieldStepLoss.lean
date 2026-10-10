import OAI.Probability.InvariantIsing.Core.LogMeanLoss
import OAI.Probability.InvariantIsing.Gaussian.GaussianTiltLinearGrowth

namespace OAI

/-! The canonical transition propagates the actual constrained-block
loss by expectation. All integrability obligations follow from the
finite-spin terminal and Gaussian exponential moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedFieldRecursion_succ {N : ℕ} (S : Finset (Spin N))
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (z : Fin N → ℝ) :
    restrictedFieldRecursion S (n + 1) b v z =
      logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
        (fun w => restrictedFieldRecursion S n (fun i => b (i + 1))
          (fun i => v (i + 1)) (z + w)) := rfl

lemma restrictedFieldRecursion_tilt_integrable {N : ℕ} (hN : 0 < N)
    (S T : Finset (Spin N)) (hS : S.Nonempty) (hT : T.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (root : ℝ≥0) (q : ℝ) (z : Fin N → ℝ) :
    Integrable (fun w => restrictedFieldRecursion T n b v (z + w))
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).tilted
        (fun w => q * restrictedFieldRecursion S n b v (z + w))) := by
  have hF := restrictedFieldRecursion_regular hN S hS n b v hb
  have hG := restrictedFieldRecursion_regular hN T hT n b v hb
  exact integrable_linearGrowth_tilted (vectorGaussianLaw N root : Measure (Fin N → ℝ))
    (vectorGaussianLaw_moments hN root)
    (fun w : Fin N → ℝ => restrictedFieldRecursion S n b v (z + w))
    (fun w : Fin N → ℝ => restrictedFieldRecursion T n b v (z + w))
    (hF.1.comp (measurable_const.add measurable_id)) (hF.2.add_left z)
    (hG.1.comp (measurable_const.add measurable_id)) (hG.2.add_left z) q

theorem restrictedFieldRecursion_step_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n + 1, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ (n + 1) b v z -
        restrictedFieldRecursion S (n + 1) b v z ≤
      ∫ w, restrictedFieldRecursion Finset.univ n (fun i => b (i + 1))
          (fun i => v (i + 1)) (z + w) -
        restrictedFieldRecursion S n (fun i => b (i + 1)) (fun i => v (i + 1)) (z + w)
        ∂(vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
          (fun w => b 0 * restrictedFieldRecursion Finset.univ n (fun i => b (i + 1))
            (fun i => v (i + 1)) (z + w)) := by
  let bs := fun i => b (i + 1)
  let vs := fun i => v (i + 1)
  have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
  let F := fun w => restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs (z + w)
  let G := fun w => restrictedFieldRecursion S n bs vs (z + w)
  change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) F -
    logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) G ≤
      ∫ w, F w - G w ∂(vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
        (fun w => b 0 * F w)
  have hiF := integrable_exp_restrictedFieldRecursion hN (Finset.univ : Finset (Spin N))
    Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z
  have hiG := integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z
  have hiFF := restrictedFieldRecursion_tilt_integrable hN Finset.univ Finset.univ
    Finset.univ_nonempty Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z
  have hiFG := restrictedFieldRecursion_tilt_integrable hN Finset.univ S
    Finset.univ_nonempty hS n bs vs hbs (v 0) (b 0) z
  have hD : Integrable (fun w => F w - G w)
      ((vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted (fun w => b 0 * F w)) :=
    hiFF.sub hiFG
  exact logMean_loss_le_tilted_mean (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) F G
    (hb 0 (by omega)) hiF hiG hD

end InvariantIsing

end

end OAI
