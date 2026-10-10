import OAI.Probability.InvariantIsing.Magnetic.RestrictedOriginalComparison
import OAI.Probability.InvariantIsing.Magnetic.RestrictedBaseCutoffProduct

namespace OAI

/-! The original cutoff spin law compared with the actual base Gibbs
product reweighted by the unperturbed cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

theorem restricted_original_weighted_comparison {N n m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C D M s₀ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hM : 0 ≤ M) (hs₀ : 0 < s₀)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let μ := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
    let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
    let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
    |(∫ z, cavityWeightedReplicaMean
      ((μ.tilted (cavityRotationHamiltonian V (diagonalPerturbedEigenvalues eig₀ J v t) J u z)).prod
        (restrictedSpinPrior Cset hCset))
      ((cavityPairLeafUnswap ⁻¹' s).indicator (fun x => Real.exp (W (cavityPairLeafUnswap x))))
      (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) ∂gaussianCoordinates) -
      (∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z)
        {x | w (cavitySpinSplit N n x.1) ≤ D}
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityDeterministicRate n m (2 * C) N * D)) / s₀ + M^2 * s₀ / 2 := by
  intro μ s W
  rw [← restricted_base_cutoff_product S hS Cset hCset U V T J eig eig₀ v u hu t w D F]
  exact restricted_original_cutoff_comparison hN S hS Cset hCset U V T I J eig eig₀ v hv u hu t
    w hw hC hD hM hs₀ herr F hF

end InvariantIsing

end

end OAI
