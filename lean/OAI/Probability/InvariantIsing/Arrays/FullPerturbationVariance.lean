import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationVariance
import OAI.Probability.InvariantIsing.Arrays.MonomialEnumeration
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation

namespace OAI

/-! Uniform variance for both terms of the actual finite perturbation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The explicit complete monomial enumeration removes the degree-cap
assumption. The diagonal perturbation is the exact eigenvalue shift proved
in `rotatedEnergy_diagonalPerturbation`. -/
theorem fullPerturbationPressure_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j| ≤ 2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a| ≤ 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let profile := tensorPathProfile I degree n treeDegree h
      let P := tensorRootTreeLaw I degree n b (fun i => profile (i + 1)) (profile 0)
      let F := tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (tensorPerturbationAmplitude N u) n
      MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 +
            C * (K + 4 * m + 8) ^ 2) / N := by
  obtain ⟨C, hC, hv⟩ := tensorPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hvbound t ht n b hb h hh h0 H hH
    degree treeDegree profile P F
  have hNm : 0 < N := by omega
  have hK' : 0 < K + 4 * m := by positivity
  have heig' : ∀ i, |diagonalPerturbedEigenvalues eig I v t i| ≤ K + 4 * m :=
    diagonalPerturbedEigenvalues_abs_le hNm eig I v hvbound t ht K heig
  have hd : ∀ j : Fin N, (∑ a, (degree j a : ℝ)) ≤ (1 : ℝ) * ((j : ℝ) + 1) := by
    intro j
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m j
  simpa only [mul_one] using hv N hN μ hμ hμinv m
    (diagonalPerturbedEigenvalues eig I v t) c (K + 4 * m) hK' heig' I degree u hu
    1 (by norm_num) hd n treeDegree b hb h hh h0 H hH

end InvariantIsing

end

end OAI
