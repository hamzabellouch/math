import OAI.Probability.InvariantIsing.Cavity.CavityRotationRestrictedIntegral
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalGroupCutoffLimit
import OAI.Probability.InvariantIsing.Cavity.CavityFactorScaling

namespace OAI

/-! The actual canonical cutoff mean, with fixed tree, is exactly the
restricted Haar Gibbs model used in the finite-replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix

namespace InvariantIsing

theorem cavity_canonical_restricted_law {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    [IsProbabilityMeasure η]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (t : ℝ) (A : CavityFactorBlocks d n)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let E := cavityBaseGroupEquiv k e g
    let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
      (cavitySpectralGroup (fun i => (E.symm i).1)) v t
    let K := t • A.1
    let L := t • A.2.1
    let C := t • A.2.2
    let τ := cavityFactorSize K L C * (1+R^2)
    (∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig
        (cavitySpectralGroup (fun i => (E.symm i).1)) u p.1).prod (uniformSpinPrior n))
      (fun x => cavityHaarRestrictedWeight (fun j => (g j,j))
        (cavityRotationVectors (cavityBaseGroupDimension k g) E)
        (cavityCanonicalGroupFrame k e g hk) K L C τ R (p,x)) F
      ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)) =
    cavityCanonicalGroupCutoffMean k e g hk μ η T lam v u t (1+R^2) A F := by
  intro E eig K L C τ
  let I := cavitySpectralGroup (fun i => (E.symm i).1)
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight (fun j => (g j,j))
    (cavityRotationVectors (depth := depth) (cavityBaseGroupDimension k g) E)
    (cavityCanonicalGroupFrame k e g hk) K L C τ R
  let κ := cavityHaarSpinPriorKernel
    (U := (a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a))
    ν (measurable_cavityRotationProbability eig I u) (uniformSpinPrior n : Measure (Spin n))
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight _ _
    (measurable_cavityRotationVectors _ E) _ K L C τ R
  have hm : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) ((measurable_of_countable F).comp measurable_snd) 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos τ).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem _ _ _ K L C τ R (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hs := cavity_bounded_disorder_dirac_shuffle μ T gaussianCoordinates η f hm hb
  change _ = ∫ V, ∫ W, ∫ z, _ ∂gaussianCoordinates ∂η ∂μ
  rw [show (∫ p, cavityWeightedReplicaMean ((ν p.1).prod (uniformSpinPrior n))
      (fun x => w (p,x)) F ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η)) =
      ∫ p, f p ∂(((μ.prod (Measure.dirac T)).prod gaussianCoordinates).prod η) by
    simp only [f,κ,cavityHaarSpinPriorKernel_apply]]
  rw [hs]
  apply integral_congr_ae
  filter_upwards [] with V
  apply integral_congr_ae
  filter_upwards [] with W
  apply integral_congr_ae
  filter_upwards [cavityRotationProbability_eq_tilted_ae eig I u hu V T] with z hz
  simp only [f,κ,cavityHaarSpinPriorKernel_apply]
  rw [show ν ((V,T),z) = _ from hz]
  congr 1
  funext x
  have he := cavityRestrictedFactor_eq_indicator K L C τ hR (le_refl _)
    (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      cavitySelectedSiteProjection (fun j => (g j,j))
        (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
        (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e g hk) W) x.1.1)
    Prod.snd x
  change cavityRestrictedFactor K L C τ R
    (cavitySelectedSiteProjection (fun j => (g j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
      (cavityGroupHaarFrames (cavityCanonicalGroupFrame k e g hk) W) x.1.1) x.2 = _
  rw [he]
  rw [cavity_radial_square_cutoff _ (fun x => norm_nonneg _) hR]
  simp only [K,L,C,E,cavityLogFactor_smul]

end InvariantIsing

end

end OAI
