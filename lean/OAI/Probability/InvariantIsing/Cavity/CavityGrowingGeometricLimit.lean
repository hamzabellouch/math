import OAI.Probability.InvariantIsing.Arrays.TensorGrowingGeometricLimit
import OAI.Probability.InvariantIsing.Cavity.CavityBasePerturbedLaw

namespace OAI

/-! The growing-depth physical minimizing sequence has every geometric
and Ward property required by the cavity lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_growing_depth_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ r, CascadeExponents (depth r) (b r))
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K)
    (heig : ∀ k i, |eig k i|≤K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧
    ∃ u : (r : ℕ) → Fin (N (φ r)) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2) ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => cavityRotationArrayLaw (μ (φ r))
        (labeledCascadeLaw (depth (ψ r)) (b (ψ r)) : Measure (LabeledTree (depth (ψ r))))
        (diagonalPerturbedEigenvalues (eig (φ r)) (I (φ r)) (v r) 1)
        (I (φ r)) (cavityBaseAmplitude (u r))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b₀ Φ=0) ∧
      (∀ a b₀, spectralDiagonalWardResidual Q ρ lam a b₀=0) := by
  have hpos k : 0<N k := by have := hN k; omega
  obtain ⟨φ,ψ,hφ,hψ,u,v,hu,hv,Q,q,hL,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩ :=
    tensor_growing_depth_geometric_limit hhaar hgauss N hN hNlim m depth b hb
      (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
      (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
      eig K hK heig I hdis hcover lam hlam ρ hρ
  have he r := cavity_base_perturbed_array_law (depth := depth (ψ r)) (hpos (φ r))
    (μ (φ r)) (eig (φ r)) (I (φ r)) (u r) (v r) 1 (b (ψ r))
  exact ⟨φ,ψ,hφ,hψ,u,v,hu,hv,Q,q,hL.congr (fun r => (he r).symm),hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩

end InvariantIsing

end

end OAI
