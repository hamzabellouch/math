import OAI.Probability.InvariantIsing.Arrays.TensorObjectiveContinuity
import OAI.Probability.InvariantIsing.Arrays.TensorLimitExistence
import OAI.Probability.InvariantIsing.Arrays.TensorArrayGeometry

namespace OAI

/-! Construction of actual perturbed Gibbs limits satisfying spectral GG and geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

/-- Haar and Gaussian concentration yield finite minimizers and a weak
limit satisfying the vector Ghirlanda–Guerra identities. -/
theorem tensorPerturbation_exists_geometric_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H) :
    ∃ u : (k : ℕ) → Fin (N k) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
      ∃ q : Fin (m + 1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) n b (h (φ k))) atTop (nhds Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) := by
  choose u v hu hv hmin using fun k => tensorPerturbationObjective_exists_minimum hhaar hgauss
    (hN k) (μ k) (hμinv k) (eig k) (c k) (I k) (t k) n b hb (h k) (hh k) (h0 k)
  obtain ⟨Q, q, φ, hφ, hL, _, hgg, hd⟩ := tensorPerturbation_minimizers_have_GG_limit
    hhaar hgauss N hN hNlim m n b hb μ hμinv eig c K hK heig I u hu v hv t ht h hh h0 H hH hmin
  have hg := tensorPerturbedArrayLaw_limit_geometry (fun k => N (φ k)) m n
    (fun k => μ (φ k)) (fun k => eig (φ k)) (fun k => c (φ k)) (fun k => I (φ k))
    (fun k => u (φ k)) (fun k => v (φ k)) (fun k => t (φ k)) b (fun k => h (φ k)) Q hL
  exact ⟨u, v, hu, hv, Q, q, φ, hφ, hL, hgg, hd, hg.1, hg.2,
    spectralGG_coordinate_nonnegative hgg hg.1 (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd⟩

end InvariantIsing

end

end OAI
