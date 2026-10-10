import OAI.Probability.InvariantIsing.Cavity.CavityOriginalRestrictedFamily
import OAI.Probability.InvariantIsing.Cavity.CavityUniformTreeLimit
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalTreeRegular
import OAI.Probability.InvariantIsing.Cavity.CavityTreeRestrictedRegular

namespace OAI

/-! The original cutoff comparison averaged over the actual random
cascade tree and all retained Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_original_restricted_tree_limit {m d n : ℕ}
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
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
    Tendsto (fun j => (∫ T, (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) T
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) ∂θ j) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (θ j)).prod gaussianCoordinates).prod (η j))) atTop (𝓝 0) := by
  intro E eig τ
  let O := fun j (T : LabeledTree (depth j)) => (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) T
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j)
  let C := fun j (T : LabeledTree (depth j)) => ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (Measure.dirac T)).prod gaussianCoordinates).prod (η j))
  have hfix : ∀ T : (j : ℕ) → LabeledTree (depth j),
      Tendsto (fun j => O j (T j)-C j (T j)) atTop (𝓝 0) := by
    intro T
    exact cavity_original_restricted_haar_limit_family N depth hN hNlim g k ek e es B₀ a₀ hk η
      l w hg hln hw μ ν T lam v hv u hu t hR hM F hF A hprob
  have havg := cavity_average_zero_of_all_selections θ (fun j T => O j T-C j T) hfix
  apply havg.congr'
  filter_upwards [] with j
  have hO := cavity_original_tree_regular (μ j) (Nat.add_pos_left (hN j) n) (g j)
    (cavityConcreteComplement es B₀) (measurable_cavityConcreteComplement es B₀)
    (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
    (u j) hR hM (fun σ => F j (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
    (fun σ => hF j _)
  have hC := cavity_restricted_tree_regular (ν j) (cavityBaseGroupDimension (k j) a₀) (E j)
    (η j) (eig j) (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j)
    (fun i => (a₀ i,i)) (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (t • A.1) (t • A.2.1) (t • A.2.2) (uniformSpinPrior n : Measure (Spin n))
    τ R hM (F j) (hF j)
  have hOi : Integrable (O j) (θ j) := integrable_of_measurable_abs_le hO.1 hO.2
  have hCi : Integrable (C j) (θ j) := integrable_of_measurable_abs_le hC.1 hC.2
  rw [integral_sub hOi hCi]
  have he := cavity_restricted_tree_average (ν j) (θ j)
    (cavityBaseGroupDimension (k j) a₀) (E j) (η j) (eig j)
    (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j)
    (fun i => (a₀ i,i)) (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (t • A.1) (t • A.2.1) (t • A.2.2) (uniformSpinPrior n : Measure (Spin n))
    τ R hM (F j) (hF j)
  exact congrArg (fun x => (∫ T, O j T ∂θ j)-x) he

end InvariantIsing

end

end OAI
