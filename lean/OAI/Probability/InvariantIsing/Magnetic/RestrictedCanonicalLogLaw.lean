import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalHaarLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedCanonicalCappedLog

namespace OAI

/-! Identification of the canonical capped logarithm with the full
original spin/leaf Gibbs probability and fresh spectral-group rotations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing


theorem restricted_canonical_capped_log_law {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))
    [IsProbabilityMeasure η] (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t cap δ : ℝ) (hcap : 0 ≤ cap) (B : CavityFactorBlocks d n) :
    (∫ V, restrictedProjectorCappedLog S hS C hC T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ B (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂μ) =
    ∫ p, restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ B p
      ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η) := by
  let E := cavityBaseGroupEquiv k e a₀
  let I := cavitySpectralGroup (fun i => (E.symm i).1)
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1) I v t
  let f := restrictedCanonicalHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ B
  have hm := measurable_restrictedCanonicalHaarLog (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ B
  have hb := restrictedCanonicalHaarLog_bound (depth := depth) S hS C hC k e a₀ hk lam v u t cap δ hcap B
  have hs := cavity_bounded_disorder_dirac_shuffle μ T gaussianCoordinates η f hm hb
  change _ = ∫ p, f p ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)
  rw [hs, restricted_canonical_capped_log_group_average S hS C hC k e a₀ hk μ η T lam v u hu t cap δ hcap B]
  apply integral_congr_ae
  apply ae_of_all
  intro V
  apply integral_congr_ae
  apply ae_of_all
  intro W
  apply integral_congr_ae
  filter_upwards [restrictedRotationProbability_eq_tilted_ae S hS eig I u hu V T] with z hz
  dsimp only [f, restrictedCanonicalHaarLog, restrictedHaarLogObservable, cavityRotationVectors]
  rw [hz, cavity_tilt_prod_left _ _ _ (measurable_of_countable _)]
  rfl

end InvariantIsing

end

end OAI
