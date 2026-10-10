import OAI.Probability.InvariantIsing.Arrays.TensorGGExistence
import OAI.Probability.InvariantIsing.Arrays.TensorSpectralIdentification

namespace OAI

/-! Actual finite perturbation minima have subsequential spectral path
identification, conditional only on the precise published concentration inputs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem tensorPerturbation_exists_identified_GG_limit
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
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    {t₀ : ℝ} (htlim : Tendsto t atTop (𝓝 t₀))
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    ∃ u : (k : ℕ) → Fin (N k) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ k j, u k j ∈ Icc (1 : ℝ) 2) ∧ (∀ k a, v k a ∈ Icc (1 : ℝ) 2) ∧
      ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
      ∃ q : Fin (m + 1) → Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) n b (h (φ k))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) ∧
      ∃ hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x,
      ∃ hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ),
        let p := spectralSpinQuantilePath Q hP hn
        (∀ a, (q a.castSucc : ℝ) = spectralGroupDiagonal ρ (fun a => t₀ * lam a) hρpos hρsum p a) ∧
          ∀ᵐ s ∂pathMeasure, ∀ a, spectralGroupQuantilePath Q hn a s =
            spectralGroupPath ρ (fun a => t₀ * lam a) hρpos hρsum p a s := by
  obtain ⟨u, v, hu, hv, Q, q, φ, hφ, hL, hgg, hd, _, _, _⟩ :=
    tensorPerturbation_exists_geometric_GG_limit hhaar hgauss N hN hNlim m n b hb μ hμinv
      eig c K hK heig I t ht h hh h0 H hH
  have hua (k : ℕ) (j : Fin (N k)) : |u k j| ≤ 2 :=
    abs_le.mpr ⟨by linarith [(hu k j).1], (hu k j).2⟩
  have hva (k : ℕ) (a : Fin m) : |v k a| ≤ 2 :=
    abs_le.mpr ⟨by linarith [(hv k a).1], (hv k a).2⟩
  have hid := tensorPerturbedArrayLaw_spectral_identification (fun k => N (φ k))
    (fun k => by have := hN (φ k); omega) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => eig (φ k)) (fun k => c (φ k))
    (fun k => I (φ k)) (fun k => hdis (φ k)) (fun k => hcover (φ k)) lam
    (fun k => hlam (φ k)) (fun k => u (φ k)) (fun k => hua (φ k))
    (fun k => v (φ k)) (fun k => hva (φ k)) (fun k => t (φ k))
    (htlim.comp hφ.tendsto_atTop) b (fun k => h (φ k)) (fun k => hh (φ k))
    (fun k => h0 (φ k)) Q hL ρ hρpos hρsum (hρ.comp hφ.tendsto_atTop)
    hgg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd
  exact ⟨u, v, hu, hv, Q, q, φ, hφ, hL, hgg, hd, hid⟩

end InvariantIsing

end

end OAI
