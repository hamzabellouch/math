import OAI.Probability.InvariantIsing.Magnetic.RestrictedZeroTreeArrayLaw
import OAI.Probability.InvariantIsing.Fields.PriorGGWardExistence
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides

namespace OAI

/-! The physical constrained model has a complete GG/Ward limit along actual minima. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem restricted_physical_GG_Ward_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (S : (k : ℕ) → Finset (Spin (N k))) (hS : ∀ k, (S k).Nonempty)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    ∃ u : (k : ℕ) → Fin (N k) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ k j, u k j∈Set.Icc (1 : ℝ) 2) ∧ (∀ k a, v k a∈Set.Icc (1 : ℝ) 2) ∧
      (∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        priorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
          (restrictedZeroTreePrior (S k) (hS k)) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) (u k) (v k)≤
        priorPerturbationObjective (cavityOrientedBaseLaw (by have := hN k; omega) (μ k))
          (restrictedZeroTreePrior (S k) (hS k)) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) u' v') ∧
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => restrictedRotationArrayLaw (S (φ k)) (hS (φ k)) (μ (φ k)) (θ (φ k))
        (diagonalPerturbedEigenvalues (eig (φ k)) (I (φ k)) (v (φ k)) 1)
        (I (φ k)) (cavityBaseAmplitude (u (φ k)))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b Φ=0) ∧
      (∀ a b, spectralDiagonalWardResidual Q ρ lam a b=0) := by
  have hpos k : 0<N k := by have := hN k; omega
  obtain ⟨u,v,hu,hv,hmin,Q,q,φ,hφ,hL,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩ :=
    priorPerturbation_exists_GG_Ward_limit hhaar hgauss N hN hNlim m 0
      (fun k => cavityOrientedBaseLaw (hpos k) (μ k))
      (fun k => cavityOrientedBaseLaw_leftInvariant (hpos k) (μ k))
      (fun k => restrictedZeroTreePrior (S k) (hS k)) eig K hK heig I hdis hcover lam hlam ρ hρ
  refine ⟨u,v,hu,hv,hmin,Q,q,φ,hφ,?_,hgg,hd,hG,hE,hP,hn,hoff,hdiag⟩
  apply hL.congr
  intro k
  exact (restricted_zero_tree_perturbed_array_law (hpos (φ k)) (S (φ k)) (hS (φ k))
    (μ (φ k)) (θ (φ k)) (eig (φ k)) (I (φ k)) (u (φ k)) (v (φ k)) 1).symm

end InvariantIsing

end

end OAI
