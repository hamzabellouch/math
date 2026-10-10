import OAI.Probability.InvariantIsing.Arrays.TensorLimitingDiagonal

namespace OAI

/-! Actual finite perturbation minima admit limiting GG arrays with constant diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorPerturbation_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v') :
    ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
      ∃ q : Fin (m + 1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) n b (h (φ k))) atTop (nhds Q) ∧
      Tendsto (fun k => tensorMinimumArrayDiagonal (N (φ k)) n (v (φ k))) atTop (nhds q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (Q : Measure (SpectralArray (m + 1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a) := by
  let L := fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k)
  let center := fun k => tensorMinimumArrayDiagonal (N k) n (v k)
  obtain ⟨Q, q, φ, hφ, hL, hc⟩ := spectralArray_center_subsequence (m + 1) L center
  refine ⟨Q, q, φ, hφ, hL, hc, ?_, ?_⟩
  · exact tensorPerturbation_minimizers_spectralGG hhaar hgauss
      (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n b hb
      (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => eig (φ k)) (fun k => c (φ k)) K hK
      (fun k => heig (φ k)) (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
      (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
      (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
      (fun k => hmin (φ k)) Q hL
  · have hco : Continuous (fun z : Fin (m + 1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
      continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
    have hc' : Tendsto (fun k a => (tensorMinimumArrayDiagonal (N (φ k)) n (v (φ k)) a : ℝ))
        atTop (nhds (fun a => (q a : ℝ))) := (hco.tendsto q).comp hc
    exact tensorPerturbation_minimizers_constantDiagonal hhaar hgauss
      (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n b hb
      (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => eig (φ k)) (fun k => c (φ k)) K hK
      (fun k => heig (φ k)) (fun k => I (φ k)) (fun k => u (φ k)) (fun k => hu (φ k))
      (fun k => v (φ k)) (fun k => hv (φ k)) (fun k => t (φ k)) (fun k => ht (φ k))
      (fun k => h (φ k)) (fun k => hh (φ k)) (fun k => h0 (φ k)) H (fun k => hH (φ k))
      (fun k => hmin (φ k)) Q hL (fun a => (q a : ℝ)) hc'

end InvariantIsing

end

end OAI
