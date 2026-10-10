import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalLogLaw
import OAI.Probability.InvariantIsing.Cavity.CavityDiracAverage

namespace OAI

/-! Restoring the common random cascade in the canonical capped
logarithmic identity, while retaining the original Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_canonical_tree_log_law {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n) :
    (∫ T, ∫ V, cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ B (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂μ ∂θ) =
    ∫ p, cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ B p
      ∂(((μ.prod θ).prod gaussianCoordinates).prod η) := by
  let f := cavityCanonicalHaarLog (depth := depth) k e a₀ hk lam v u t cap δ B
  have hm := measurable_cavityCanonicalHaarLog (depth := depth) k e a₀ hk lam v u t cap δ B
  have hb := cavityCanonicalHaarLog_bound (depth := depth) k e a₀ hk lam v u t cap δ hcap B
  have hfix (T : LabeledTree depth) :=
    cavity_canonical_capped_log_law k e a₀ hk μ η T lam v u hu t cap δ hcap B
  change (∫ T, ∫ V, cavityProjectorCappedLog T
    (fun a => t*lam a+2*perturbationScale N*v a) u t cap δ B
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂μ ∂θ) =
    ∫ p, f p ∂(((μ.prod θ).prod gaussianCoordinates).prod η)
  simp_rw [hfix]
  exact cavity_bounded_dirac_average μ θ gaussianCoordinates η f hm hb

end InvariantIsing

end

end OAI
