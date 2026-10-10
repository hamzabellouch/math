import OAI.Probability.InvariantIsing.Core.TiltedRelativeEntropy
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldStepLoss

namespace OAI

/-! Exact weighted conditional-entropy loss at one actual constrained
Gaussian step. The ordinary entropy is bounded with no lower cutoff on
the positive cascade exponent. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron InformationTheory
open scoped NNReal

namespace InvariantIsing

theorem restrictedFieldRecursion_step_entropy {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n + 1, 0 < b i) (hb1 : b 0 ≤ 1) (z : Fin N → ℝ) :
    let F := fun w => restrictedFieldRecursion Finset.univ n (fun i => b (i + 1))
      (fun i => v (i + 1)) (z + w)
    let G := fun w => restrictedFieldRecursion S n (fun i => b (i + 1))
      (fun i => v (i + 1)) (z + w)
    let μ := (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
    klDiv (μ.tilted (fun w => b 0 * G w)) (μ.tilted (fun w => b 0 * F w)) ≠ ⊤ ∧
      (klDiv (μ.tilted (fun w => b 0 * G w)) (μ.tilted (fun w => b 0 * F w))).toReal +
        (∫ w, F w - G w ∂μ.tilted (fun w => b 0 * G w)) ≤
      restrictedFieldRecursion Finset.univ (n + 1) b v z -
        restrictedFieldRecursion S (n + 1) b v z := by
  dsimp only
  let bs := fun i => b (i + 1)
  let vs := fun i => v (i + 1)
  have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
  let F := fun w => restrictedFieldRecursion (Finset.univ : Finset (Spin N)) n bs vs (z + w)
  let G := fun w => restrictedFieldRecursion S n bs vs (z + w)
  let μ := (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
  have hF := integrable_exp_restrictedFieldRecursion hN Finset.univ Finset.univ_nonempty
    n bs vs hbs (v 0) (b 0) z
  have hG := integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z
  have hGF := restrictedFieldRecursion_tilt_integrable hN S Finset.univ hS
    Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z
  have hGG := restrictedFieldRecursion_tilt_integrable hN S S hS hS
    n bs vs hbs (v 0) (b 0) z
  have hD : Integrable (fun w => F w - G w) (μ.tilted (fun w => b 0 * G w)) := hGF.sub hGG
  exact ⟨(tilted_pair_entropy_identity μ F G (hb 0 (by omega)) hF hG hD).1,
    tilted_pair_entropy_budget μ F G (hb 0 (by omega)) hb1 hF hG hD⟩

end InvariantIsing

end

end OAI
