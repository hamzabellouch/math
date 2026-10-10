import OAI.Probability.InvariantIsing.Arrays.TensorGrowingDepthSelection
import OAI.Probability.InvariantIsing.Arrays.TensorGrowingPerturbedWard
import OAI.Probability.InvariantIsing.Spectral.SpectralPartition

namespace OAI

/-! The growing-depth physical minimizing sequence has every geometric
and Ward property required by the cavity lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem tensor_growing_depth_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ r, CascadeExponents (depth r) (b r))
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
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
      Tendsto (fun r => tensorPerturbedArrayLaw (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r))
        (u r) (v r) 1 (depth (ψ r)) (b (ψ r)) (fun _ => 0)) atTop (𝓝 Q) ∧
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
  obtain ⟨φ,ψ,hφ,hψ,u,v,hu,hv,Q,q,hL,hgg,hd⟩ :=
    tensor_growing_depth_minimizers_limit hhaar hgauss N hN hNlim m depth b hb μ hμinv eig K hK heig I
  have hpos r : 0<N (φ r) := by have := hN (φ r); omega
  have hG := spectralArray_limit_gram hL (fun r => tensorPerturbedArrayLaw_gram
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u r) (v r) 1 (depth (ψ r)) (b (ψ r)) (fun _ => 0))
  have hE (e : ℕ → ℕ) (he : Function.Injective e) :=
    spectralArray_limit_reindex hL e (fun r => tensorPerturbedArrayLaw_reindex
      (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u r) (v r) 1
      (depth (ψ r)) (b (ψ r)) (fun _ => 0) e he)
  have hP := spectralArray_limit_partition hL (fun r => tensorPerturbedArrayLaw_partition (hpos r)
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (hdis (φ r)) (hcover (φ r)) (u r) (v r) 1
    (depth (ψ r)) (b (ψ r)) (fun _ => 0))
  have hn := spectralGG_coordinate_nonnegative hgg hG (fun a => (q a : ℝ))
    (fun a => (q a).property.1) hd
  have hua r j : |u r j|≤2 := abs_le.mpr ⟨by linarith [(hu r j).1],(hu r j).2⟩
  have hva r a : |v r a|≤2 := abs_le.mpr ⟨by linarith [(hv r a).1],(hv r a).2⟩
  have hw := tensorGrowingPerturbedArrayLaw_ward_limits (fun r => N (φ r)) hpos
    (hNlim.comp hφ.tendsto_atTop) m (fun r => depth (ψ r)) (fun r => μ (φ r))
    (fun r => hμinv (φ r)) (fun r => eig (φ r)) (fun _ _ => 0) (fun r => I (φ r))
    (fun r => hdis (φ r)) (fun r => hcover (φ r)) lam (fun r => hlam (φ r))
    u hua v hva (fun _ => 1) tendsto_const_nhds (fun r => b (ψ r)) (fun _ _ => 0)
    (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ (hρ.comp hφ.tendsto_atTop)
  simp only [one_mul] at hw
  exact ⟨φ,ψ,hφ,hψ,u,v,hu,hv,Q,q,hL,hgg,hd,hG,hE,hP,hn,hw.1,hw.2⟩

end InvariantIsing

end

end OAI
