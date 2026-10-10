import OAI.Probability.InvariantIsing.Arrays.TensorPerturbedWardLimit
import OAI.Probability.InvariantIsing.Spectral.SpectralCanonicalIdentification
import OAI.Probability.InvariantIsing.Arrays.TensorArrayGeometry

namespace OAI

/-! Enriched Ghirlanda–Guerra limits have the reconstructed spectral
paths and constant diagonals. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem tensorPerturbedArrayLaw_spectral_identification
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
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) :
    ∃ hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x,
    ∃ hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ),
      let p := spectralSpinQuantilePath Q hP hn
      (∀ a, q a.castSucc = spectralGroupDiagonal ρ (fun a => t₀ * lam a) hρpos hρsum p a) ∧
        ∀ᵐ s ∂pathMeasure, ∀ a, spectralGroupQuantilePath Q hn a s =
          spectralGroupPath ρ (fun a => t₀ * lam a) hρpos hρsum p a s := by
  have hG := tensorPerturbedArrayLaw_limit_geometry N m n μ eig c I u v t b h Q hL
  have hn := spectralGG_coordinate_nonnegative hgg hG.1 q hq hd
  have hP := spectralArray_limit_partition hL (fun k =>
    tensorPerturbedArrayLaw_partition (hN k) (μ k) (eig k) (c k) (I k) (hdis k) (hcover k)
      (u k) (v k) (t k) n b (h k))
  obtain ⟨hoff, hdiag⟩ := tensorPerturbedArrayLaw_ward_limits N hN hNlim m n μ hμinv eig c I
    hdis hcover lam hlam u hu v hv t ht b h hh h0 Q hL ρ hρ
  exact ⟨hP, hn, spectralCanonical_identification hgg hG.1 q hq hd hG.2 hP hn
    ρ (fun a => t₀ * lam a) hρpos hρsum hoff hdiag⟩

end InvariantIsing

end

end OAI
