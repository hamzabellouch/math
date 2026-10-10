import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockSpinEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityRootedTestMean

namespace OAI

/-! Coordinate averaging for the actual rooted constrained block spin test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def cavityRootedBlockDepthTest {d k n : ℕ} (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n) : ℝ :=
  (k : ℝ)⁻¹ * ∑ j, cavityRootedSpinDepthTest a j σ

lemma cavityRootedBlockDepthTest_eq {d k n : ℕ} (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n) :
    cavityRootedBlockDepthTest a σ =
      a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) *
        ((k : ℝ)⁻¹ * ∑ j, spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)) := by
  simp only [cavityRootedBlockDepthTest, cavityRootedSpinDepthTest, ← Finset.mul_sum]
  ring

lemma integral_cavityRootedBlockDepthTest {d k n : ℕ}
    (μ : Measure (ℕ → CavitySpinState d k n)) [IsProbabilityMeasure μ]
    (a : ℕ → ℝ) {C : ℝ} (ha : ∀ i, |a i| ≤ C) :
    (∫ σ, cavityRootedBlockDepthTest a σ ∂μ) =
      (k : ℝ)⁻¹ * ∑ j, ∫ σ, cavityRootedSpinDepthTest a j σ ∂μ := by
  unfold cavityRootedBlockDepthTest
  rw [integral_const_mul, integral_finsetSum]
  intro j _
  exact integrable_of_measurable_abs_le (measurable_cavityRootedSpinDepthTest a j)
    (cavityRootedSpinDepthTest_abs_le a j ha)

lemma restricted_rooted_block_evaluation {d k : ℕ} (hk : 0 < k)
    (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
    (μ : Measure (ℕ → CavitySpinState d k h.depth)) [IsProbabilityMeasure μ]
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C)
    (hcoord : ∀ j : Fin k,
      (∫ σ, cavityRootedSpinDepthTest (fun i => Φ (q (fieldDepthLevel h i))) j σ ∂μ) =
        ∫ t, Φ (q (fieldLevelIndex h t)) *
          (∫ z, restrictedPairCoordinateMean hk T hT h.depth (chainExponent h.cut)
            (fieldStepVariance h)
            (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
            (fieldLevelIndex h t) j z
            ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _)) ∂pathMeasure) :
    (∫ σ, cavityRootedBlockDepthTest (fun i => Φ (q (fieldDepthLevel h i))) σ ∂μ) =
      ∫ t, Φ (q (fieldLevelIndex h t)) * restrictedBlockOverlapPath hk T hT h t ∂pathMeasure := by
  rw [integral_cavityRootedBlockDepthTest μ _ (fun i => hΦ _)]
  simp_rw [hcoord]
  let a := fun (j : Fin k) (i : Fin (h.depth + 1)) => Φ (q i) *
    (∫ z, restrictedPairCoordinateMean hk T hT h.depth (chainExponent h.cut)
      (fieldStepVariance h)
      (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1)
      i j z ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _))
  change (k : ℝ)⁻¹ * (∑ j, ∫ s, a j (fieldLevelIndex h s) ∂pathMeasure) = _
  have hi (j : Fin k) : Integrable (fun s => a j (fieldLevelIndex h s)) pathMeasure :=
    integrable_fieldLevelIndex h (a j)
  rw [← integral_finsetSum _ (fun j _ => hi j), ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  dsimp only [a]
  change _ = Φ (q (fieldLevelIndex h s)) *
    restrictedBlockPairMean hk T hT h (fun _ => 0) (fieldLevelIndex h s)
  rw [restrictedBlockPairMean_eq_average, ← Finset.mul_sum]
  simp only [vectorGaussianLaw, ProbabilityMeasure.coe_mk]
  ring

end InvariantIsing

end

end OAI
