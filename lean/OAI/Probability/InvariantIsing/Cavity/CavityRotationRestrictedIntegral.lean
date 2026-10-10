import OAI.Probability.InvariantIsing.Cavity.CavityRotationVectors
import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedWeight
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactorIndicator
import OAI.Probability.InvariantIsing.Cavity.CavityProductDisorderWeighted

namespace OAI

/-! The product-law restricted Gibbs average equals the iterated physical
rotation/tree/fresh-frame/Gaussian integral, with the original tilt retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_rotation_restricted_integral {N m depth q d k r : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (dims : Fin m → ℕ) (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    (η : Measure ((a : Fin m) → Orthogonal (dims a))) [IsProbabilityMeasure η]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (e : Fin d → Fin m × Fin q)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin k) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    (∫ p, cavityWeightedReplicaMean ((cavityRotationProbability eig I u p.1).prod π)
      (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors dims E) A₀ K L C T B (p,x))
      F ∂(((μ.prod θ).prod gaussianCoordinates).prod η)) =
    ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) V.2).tilted
        (cavityRotationHamiltonian (matrixRotation V.1⁻¹) eig I u z)).prod π)
      ({x | ‖cavitySelectedSiteProjection e (cavityGroupSpinCoordinates dims E V.1)
        (cavityGroupHaarFrames A₀ W) x.1.1‖ ≤ B}.indicator (fun x => Real.exp
        (cavityLogFactor K L C
          (cavitySelectedSiteProjection e (cavityGroupSpinCoordinates dims E V.1)
            (cavityGroupHaarFrames A₀ W) x.1.1) x.2))) F
      ∂gaussianCoordinates ∂η ∂μ.prod θ := by
  let P := (μ.prod θ).prod gaussianCoordinates
  let ν := cavityRotationProbability (depth := depth) eig I u
  let w := cavityHaarRestrictedWeight e (cavityRotationVectors (depth := depth) dims E) A₀ K L C T B
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (dims a))
    ν (measurable_cavityRotationProbability eig I u) π
  let f := fun p => cavityWeightedReplicaMean (κ p) (fun x => w (p,x)) F
  have hw : Measurable w := measurable_cavityHaarRestrictedWeight e
    (cavityRotationVectors dims E) (measurable_cavityRotationVectors dims E) A₀ K L C T B
  have htest : Measurable (fun p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (dims a))) ×
      (Fin r → (Spin N × LabeledLeaf depth) × Spin k) => F p.2) :=
    (measurable_of_countable F).comp measurable_snd
  have hf : Measurable f := by
    have hh := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable
      w hw (fun p => F p.2) htest 0
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hb p : |f p| ≤ M := by
    have hh := cavityRegularizedReplicaMean_abs_le (κ p) (fun x => w (p,x))
      (hw.comp measurable_prodMk_left) F (measurable_of_countable F)
      (Real.exp_pos T).le hM (δ := 0) le_rfl
      (fun x => cavityHaarRestrictedWeight_mem e (cavityRotationVectors dims E) A₀ K L C T B (p,x)) hF
    simpa only [f,cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh
  have hshuffle := cavity_bounded_disorder_shuffle (μ.prod θ) gaussianCoordinates η f hf hb
  suffices (∫ p, f p ∂P.prod η) = _ by
    simpa only [f, κ, cavityHaarSpinPriorKernel_apply, P, ν, w] using this
  rw [hshuffle]
  apply integral_congr_ae
  filter_upwards [] with V
  apply integral_congr_ae
  filter_upwards [] with W
  apply integral_congr_ae
  filter_upwards [cavityRotationProbability_eq_tilted_ae eig I u hu V.1 V.2] with z hz
  simp only [f, κ, cavityHaarSpinPriorKernel_apply]
  rw [show ν (V,z) = _ from hz]
  congr 1
  funext x
  exact cavityRestrictedFactor_eq_indicator K L C T hB hT
    (fun x : (Spin N × LabeledLeaf depth) × Spin k =>
      cavitySelectedSiteProjection e (cavityGroupSpinCoordinates dims E V.1)
        (cavityGroupHaarFrames A₀ W) x.1.1) Prod.snd x

end InvariantIsing

end

end OAI
