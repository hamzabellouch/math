import OAI.Probability.InvariantIsing.Arrays.TensorGrowingGeometricLimit

namespace OAI

/-! Any prescribed sequence of actual finite minima admits a geometric GG
limit. The minimizers are retained, so their pressure envelope can telescope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem tensor_fixed_minimum_geometric_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
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
      tensorPerturbationObjective (μ k) (eig k) (fun _ => 0) (I k) 1 depth b
        (fun _ => 0) (u k) (v k) ≤
      tensorPerturbationObjective (μ k) (eig k) (fun _ => 0) (I k) 1 depth b (fun _ => 0) u' v') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => tensorPerturbedArrayLaw (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r))
        (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0)) atTop (𝓝 Q) ∧
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
  let laws := fun k => tensorPerturbedArrayLaw (μ k) (eig k) (fun _ => 0) (I k)
    (u k) (v k) 1 depth b (fun _ => 0)
  let center := fun k => tensorMinimumArrayDiagonal (N k) depth (v k)
  obtain ⟨Q,q,φ,hφ,hL,hc⟩ := spectralArray_center_subsequence (m+1) laws center
  have hNl := hNlim.comp hφ.tendsto_atTop
  have hpos r : 0<N (φ r) := by have := hN (φ r); omega
  have hgg := tensorPerturbation_minimizers_spectralGG hhaar hgauss (fun r => N (φ r))
    (fun r => hN (φ r)) hNl m depth b hb (fun r => μ (φ r)) (fun r => hμinv (φ r))
    (fun r => eig (φ r)) (fun _ _ => 0) K hK (fun r => heig (φ r)) (fun r => I (φ r))
    (fun r => u (φ r)) (fun r => hu (φ r)) (fun r => v (φ r)) (fun r => hv (φ r))
    (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
    (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hmin (φ r)) Q hL
  have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  have hd := tensorPerturbation_minimizers_constantDiagonal hhaar hgauss (fun r => N (φ r))
    (fun r => hN (φ r)) hNl m depth b hb (fun r => μ (φ r)) (fun r => hμinv (φ r))
    (fun r => eig (φ r)) (fun _ _ => 0) K hK (fun r => heig (φ r)) (fun r => I (φ r))
    (fun r => u (φ r)) (fun r => hu (φ r)) (fun r => v (φ r)) (fun r => hv (φ r))
    (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
    (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hmin (φ r)) Q hL
    (fun a => (q a : ℝ)) ((hco.tendsto q).comp hc)
  have hG := spectralArray_limit_gram hL (fun r => tensorPerturbedArrayLaw_gram
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0))
  have hE (e : ℕ → ℕ) (he : Function.Injective e) :=
    spectralArray_limit_reindex hL e (fun r => tensorPerturbedArrayLaw_reindex
      (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0) e he)
  have hP := spectralArray_limit_partition hL (fun r => tensorPerturbedArrayLaw_partition (hpos r)
    (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) (hdis (φ r)) (hcover (φ r))
    (u (φ r)) (v (φ r)) 1 depth b (fun _ => 0))
  have hn := spectralGG_coordinate_nonnegative hgg hG (fun a => (q a : ℝ))
    (fun a => (q a).property.1) hd
  have hua r j : |u (φ r) j|≤2 := abs_le.mpr ⟨by linarith [(hu (φ r) j).1],(hu (φ r) j).2⟩
  have hva r a : |v (φ r) a|≤2 := abs_le.mpr ⟨by linarith [(hv (φ r) a).1],(hv (φ r) a).2⟩
  have hw := tensorGrowingPerturbedArrayLaw_ward_limits (fun r => N (φ r)) hpos hNl m
    (fun _ => depth) (fun r => μ (φ r)) (fun r => hμinv (φ r)) (fun r => eig (φ r))
    (fun _ _ => 0) (fun r => I (φ r)) (fun r => hdis (φ r)) (fun r => hcover (φ r))
    lam (fun r => hlam (φ r)) (fun r => u (φ r)) hua (fun r => v (φ r)) hva
    (fun _ => 1) tendsto_const_nhds (fun _ => b) (fun _ _ => 0)
    (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ (hρ.comp hφ.tendsto_atTop)
  simp only [one_mul] at hw
  exact ⟨φ,hφ,Q,q,hL,hgg,hd,hG,hE,hP,hn,hw.1,hw.2⟩

end InvariantIsing

end

end OAI
