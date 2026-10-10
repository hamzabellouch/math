import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalGroupAverage
import OAI.Probability.InvariantIsing.Cavity.CavityHaarCutoffLimit

namespace OAI

/-! The original full-system cutoff and its actual fresh-group Gibbs
representation have the same limit after deterministic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Matrix Topology

namespace InvariantIsing

def cavityCanonicalGroupCutoffMean {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N))
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) : ℝ :=
  let E := cavityBaseGroupEquiv k e g
  let A := cavityCanonicalGroupFrame k e g hk
  ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
    (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
          (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (uniformSpinPrior n))
    ({x | 1+‖cavitySelectedSiteProjection (fun j => (g j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
      (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
        Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
          (cavitySelectedSiteProjection (fun j => (g j,j))
            (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
            (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ

theorem cavity_original_group_cutoff_limit {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × Spin n) × LabeledLeaf (depth j)) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A₀}) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) v t)
        u D (F j) (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      cavityCanonicalGroupCutoffMean (k j) (e j) a₀ (hk j) (ν j) (η j) (T j)
        lam v u t D A₀ (fun σ => F j (fun i => cavityPairLeafUnswap (σ i))))
      atTop (𝓝 0) := by
  have hh := cavity_haar_cutoff_limit N depth hN hNlim g k ek e es B₀ a₀ l w hg hln hw
    μ ν T lam v hv u hu t hD hM F hF A₀ hprob
  apply hh.congr'
  filter_upwards [] with j
  congr 1
  exact cavity_canonical_weighted_average (k j) (e j) a₀ (hk j) (ν j) (η j)
    (T j) lam v u hu t D A₀ (fun σ => F j (fun i => cavityPairLeafUnswap (σ i)))
    hM (fun σ => hF j _)

end InvariantIsing

end

end OAI
