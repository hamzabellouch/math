import OAI.Probability.InvariantIsing.Arrays.TensorSpectralIdentification
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayEnergy

namespace OAI

/-! Interaction energy in the actual enriched GG limit equals the
finite-spectrum variational energy, before multiplication by temperature. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem tensorPerturbedArrayLaw_interactionEnergy_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (ht₀ : 0 ≤ t₀) :
    ∃ hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x,
    ∃ hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ),
      Tendsto (fun k => tensorNamespacedReplicaAverage (μ k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k)) n b
        (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U (σ : Fin 1 → Spin (N k) × LabeledLeaf n) =>
          (N k : ℝ)⁻¹ * rotatedEnergy (eig k) (specialRotation U) (σ 0).1)) atTop
        (𝓝 (finiteInteractionEnergy ρ lam hρpos hρsum t₀ (spectralSpinQuantilePath Q hP hn))) := by
  obtain ⟨hP, hn, hid⟩ := tensorPerturbedArrayLaw_spectral_identification N hN hNlim m n μ hμinv
    eig c I hdis hcover lam hlam u hu v hv t ht b h hh h0 Q hL ρ hρpos hρsum hρ hgg q hq hd
  refine ⟨hP, hn, ?_⟩
  have he (k : ℕ) : (∫ x, spectralArrayInteractionEnergy lam x
      ∂(tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k) :
        Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage (μ k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k)) n b
        (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U (σ : Fin 1 → Spin (N k) × LabeledLeaf n) =>
          (N k : ℝ)⁻¹ * rotatedEnergy (eig k) (specialRotation U) (σ 0).1) :=
    tensorNamespacedArrayLaw_interactionEnergy (μ k) _ (eig k) (c k) (I k) (hdis k) (hcover k)
      lam (hlam k) _ _ b _ (h k)
  have hlim := spectralArrayInteractionEnergy_weak_limit hL lam
  simp_rw [he] at hlim
  rw [spectralArrayInteractionEnergy_eq_finiteEnergy Q q hd ρ lam hρpos hρsum ht₀
    (spectralSpinQuantilePath Q hP hn) hid.1] at hlim
  exact hlim

end InvariantIsing

end

end OAI
