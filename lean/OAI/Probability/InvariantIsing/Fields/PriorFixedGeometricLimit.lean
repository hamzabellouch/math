import OAI.Probability.InvariantIsing.Fields.PriorGGExistence

namespace OAI

/-! Every prescribed sequence of actual prior minima has a geometric GG subsequence. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem prior_minimizers_geometric_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) (u k) (v k)≤
        priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) u' v') :
      ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => priorPerturbedArrayLaw (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) := by
  let L := fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
    (u k) (v k) (t k) (h k)
  let center := fun k => tensorMinimumArrayDiagonal (N k) n (v k)
  obtain ⟨Q,q,φ,hφ,hL,hc⟩ := spectralArray_center_subsequence (m+1) L center
  have hgg := priorPerturbation_minimizers_spectralGG hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => ν (φ k))
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL
  have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  have hd := priorPerturbation_minimizers_constantDiagonal hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => ν (φ k))
    (fun k => eig (φ k)) (fun k => c (φ k)) K hK (fun k => heig (φ k))
    (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
    (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
    (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
    (fun k => hmin (φ k)) Q hL (fun a => (q a : ℝ)) ((hco.tendsto q).comp hc)
  have hg := spectralArray_limit_gram hL (fun k => priorPerturbedArrayLaw_gram
    (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
    (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)))
  have hr : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q := by
    intro e he
    exact spectralArray_limit_reindex hL e (fun k => priorPerturbedArrayLaw_reindex
      (μ (φ k)) (ν (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
      (u (φ k)) (v (φ k)) (t (φ k)) (h (φ k)) e he)
  exact ⟨Q,q,φ,hφ,hL,hgg,hd,hg,hr,
    spectralGG_coordinate_nonnegative hgg hg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd⟩

end InvariantIsing

end

end OAI
