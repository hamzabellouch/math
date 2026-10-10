import OAI.Probability.InvariantIsing.Arrays.TensorArrayResidual
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationObjective
import OAI.Probability.InvariantIsing.Arrays.TensorGGRate

namespace OAI

/-! GG estimates for actual tensor perturbation minimizers in spectral-array form. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem tensorPerturbation_minimizers_arrayResidual_bound (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
        ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
      perturbationScale N ≤ 1 / 32 → contactStep N ≤ 1 / 4 →
      (∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective μ eig c I t n b h u v ≤
          tensorPerturbationObjective μ eig c I t n b h u' v') →
      ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q + 1),
      ∀ D : SpectralBlock (m + 1) (q + 1) → ℝ, Continuous D →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |D x| ≤ B) →
      |spectralMonomialResidual
        (tensorNamespacedArrayLaw μ (diagonalPerturbedEigenvalues eig I v t) c I degree
          (tensorPerturbationAmplitude N u) n b treeDegree h)
        (q + 1) i D (Fin.lastCases (treeDegree j) (degree j))| ≤ tensorContactGGRate N j m L B := by
  obtain ⟨C, hC, hgg⟩ := fullPerturbationPressure_minimumGG hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    degree treeDegree L he hs hmin j q i D hD B hB hDb
  let : IsProbabilityMeasure μ := hμ
  have hc := tensorPerturbation_minimum_coordinates μ eig c I t n b h u v hu hv hmin
  let e := Equiv.swap 0 i
  have hg := hgg N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    he hs hc.1 hc.2 j q B hB (permutedSpectralBlockTest I n e D)
    (measurable_permutedSpectralBlockTest I n e D hD) (fun U σ => hDb _)
  have hr := tensorNamespacedArrayLaw_residual μ (diagonalPerturbedEigenvalues eig I v t) c I degree
    (tensorPerturbationAmplitude N u) n b treeDegree h j e D hD
  have hei : e 0 = i := Equiv.swap_apply_left 0 i
  rw [hei] at hr
  rw [hr]
  exact hg

end InvariantIsing

end

end OAI
