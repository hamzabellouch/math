import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalHaarLog

namespace OAI

/-! Identification of the canonical capped logarithm with the full
original spin/leaf Gibbs probability and fresh spectral-group rotations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing


theorem cavity_canonical_capped_log_law {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n) :
    (∫ V, cavityProjectorCappedLog T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ B (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂μ) =
    ∫ p, cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ B p
      ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η) := by
  let E := cavityBaseGroupEquiv k e a₀
  let I := cavitySpectralGroup (fun i => (E.symm i).1)
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1) I v t
  let f := cavityCanonicalHaarLog (depth := depth) k e a₀ hk lam v u t cap δ B
  have hm := measurable_cavityCanonicalHaarLog (depth := depth) k e a₀ hk lam v u t cap δ B
  have hb := cavityCanonicalHaarLog_bound (depth := depth) k e a₀ hk lam v u t cap δ hcap B
  have hs := cavity_bounded_disorder_dirac_shuffle μ T gaussianCoordinates η f hm hb
  change _ = ∫ p, f p ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)
  rw [hs, cavity_canonical_capped_log_group_average k e a₀ hk μ η T lam v u hu t cap δ hcap B]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  apply integral_congr_ae
  filter_upwards [cavityRotationProbability_eq_tilted_ae eig I u hu V T] with z hz
  dsimp only [f, cavityCanonicalHaarLog, cavityHaarLogObservable, cavityRotationVectors]
  rw [hz, cavity_tilt_prod_left _ _ _ (measurable_of_countable _)]
  rfl

end InvariantIsing

end

end OAI
