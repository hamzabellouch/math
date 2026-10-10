import OAI.Probability.InvariantIsing.Fields.PriorGGExistence
import OAI.Probability.InvariantIsing.Fields.PriorPerturbedWardLimits
import OAI.Probability.InvariantIsing.Spectral.SpectralPartition

namespace OAI

/-! Actual fixed-prior minima admit geometric limits with both Ward identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorPerturbedArrayLaw_partition {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I=Finset.univ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ∀ᵐ x ∂(priorPerturbedArrayLaw μ ν eig c I u v t h : Measure (SpectralArray (m+1))),
      SpectralPartitionGeometry m x := by
  unfold priorPerturbedArrayLaw priorNamespacedArrayLaw
  exact spectralArrayLaw_partition hN _ _ _ _ hdis hcover _ _ _

theorem priorPerturbation_exists_GG_Ward_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (ρ : Fin m → ℝ) (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    ∃ u : (k : ℕ) → Fin (N k) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ k j, u k j∈Set.Icc (1 : ℝ) 2) ∧ (∀ k a, v k a∈Set.Icc (1 : ℝ) 2) ∧
      (∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        priorPerturbationObjective (μ k) (ν k) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) (u k) (v k)≤
          priorPerturbationObjective (μ k) (ν k) (eig k) (fun _ => 0) (I k) 1 (fun _ => 0) u' v') ∧
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => priorPerturbedArrayLaw (μ (φ k)) (ν (φ k)) (eig (φ k)) (fun _ => 0)
        (I (φ k)) (u (φ k)) (v (φ k)) 1 (fun _ => 0)) atTop (𝓝 Q) ∧
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
  obtain ⟨u,v,hu,hv,hmin,Q,q,φ,hφ,hL,hgg,hd,hG,hE,hn⟩ :=
    priorPerturbation_exists_geometric_GG_limit hhaar hgauss N hN hNlim m n μ hμinv ν
      eig (fun _ _ => 0) K hK heig I (fun _ => 1) (fun _ => by norm_num)
      (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl) 0 (fun _ => le_rfl)
  have hpos k : 0<N (φ k) := by have := hN (φ k); omega
  have hpart := spectralArray_limit_partition hL (fun k => priorPerturbedArrayLaw_partition
    (hpos k) (μ (φ k)) (ν (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k))
    (hdis (φ k)) (hcover (φ k)) (u (φ k)) (v (φ k)) 1 (fun _ => 0))
  have hua k j : |u (φ k) j|≤2 := abs_le.mpr ⟨by linarith [(hu (φ k) j).1],(hu (φ k) j).2⟩
  have hva k a : |v (φ k) a|≤2 := abs_le.mpr ⟨by linarith [(hv (φ k) a).1],(hv (φ k) a).2⟩
  have hw := priorPerturbedArrayLaw_ward_limits (fun k => N (φ k)) hpos
    (hNlim.comp hφ.tendsto_atTop) m n (fun k => μ (φ k)) (fun k => hμinv (φ k))
    (fun k => ν (φ k)) (fun k => eig (φ k)) (fun _ _ => 0) (fun k => I (φ k))
    (fun k => hdis (φ k)) (fun k => hcover (φ k)) lam (fun k => hlam (φ k))
    (fun k => u (φ k)) hua (fun k => v (φ k)) hva (fun _ => 1) tendsto_const_nhds
    (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ (hρ.comp hφ.tendsto_atTop)
  simp only [one_mul] at hw
  exact ⟨u,v,hu,hv,hmin,Q,q,φ,hφ,hL,hgg,hd,hG,hE,hpart,hn,hw.1,hw.2⟩

end InvariantIsing

end

end OAI
