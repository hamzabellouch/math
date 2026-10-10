import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalRestrictedLaw

namespace OAI

/-! The original cutoff spin law and the concrete restricted fresh-Haar
law agree asymptotically after coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_original_restricted_haar_limit {m d n : ℕ}
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
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) v t
    let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) v t)
        u (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) u p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (Measure.dirac (T j))).prod gaussianCoordinates).prod (η j)))
      atTop (𝓝 0) := by
  intro E eig τ
  have hh := cavity_original_group_cutoff_limit N depth hN hNlim g k ek e es B₀ a₀ hk η
    l w hg hln hw μ ν T lam v hv u hu t (le_add_of_nonneg_right (sq_nonneg R)) hM
    (fun j σ => F j (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
    (fun j σ => hF j _) A hprob
  apply hh.congr'
  filter_upwards [] with j
  have he := cavity_canonical_restricted_law (k j) (e j) a₀ (hk j) (ν j) (η j)
    (T j) lam v u hu t A hR hM (F j) (hF j)
  dsimp only at he
  rw [he]
  rfl

end InvariantIsing

end

end OAI
