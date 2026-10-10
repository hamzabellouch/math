import OAI.Probability.InvariantIsing.Arrays.TensorFixedMinimumLimit
import OAI.Probability.InvariantIsing.Cavity.CavityBasePerturbedLaw

namespace OAI

/-! Physical Haar arrays along any given sequence of zero-field minima
have the complete geometric GG/Ward subsequence used by the lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_fixed_minimum_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K)
    (heig : ∀ k i, |eig k i|≤K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
        (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) (u k) (v k) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
        (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) u' v') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => cavityRotationArrayLaw (μ (φ r))
        (labeledCascadeLaw depth b : Measure (LabeledTree depth))
        (diagonalPerturbedEigenvalues (eig (φ r)) (I (φ r)) (v (φ r)) 1)
        (I (φ r)) (cavityBaseAmplitude (u (φ r)))) atTop (𝓝 Q) ∧
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
  obtain ⟨φ,hφ,Q,q,hL,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩ :=
    tensor_fixed_minimum_geometric_limit hhaar hgauss N hN hNlim m depth b hb
      (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
      (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
      eig K hK heig I hdis hcover lam hlam ρ hρ u v hu hv hmin
  refine ⟨φ,hφ,Q,q,?_,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩
  apply hL.congr
  intro r
  exact (cavity_base_perturbed_array_law (hpos (φ r)) (μ (φ r))
    (eig (φ r)) (I (φ r)) (u (φ r)) (v (φ r)) 1 b).symm

end InvariantIsing

end

end OAI
