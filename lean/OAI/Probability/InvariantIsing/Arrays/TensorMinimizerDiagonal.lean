import OAI.Probability.InvariantIsing.Arrays.TensorArrayDiagonal
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationObjective

namespace OAI

/-! Actual minimizers have compact-centered spectral diagonal fluctuations. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorPerturbation_minimizers_diagonal_bound (hhaar : HaarConcentrationInput)
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
      ∀ i : ℕ, ∀ a : Fin m,
      (∫ x, |(x (i, i) a.castSucc : ℝ) - spectralDiagonalCenter (diagonalMinimumCenter N (v a))|
        ∂(tensorNamespacedArrayLaw μ (diagonalPerturbedEigenvalues eig I v t) c I degree
          (tensorPerturbationAmplitude N u) n b treeDegree h : Measure (SpectralArray (m + 1)))) ≤
        diagonalContactRate N L := by
  obtain ⟨C, hC, hvar⟩ := fullPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    degree treeDegree L he hs hmin i a
  let : IsProbabilityMeasure μ := hμ
  have hNp : 0 < N := by omega
  have hua : ∀ j, |u j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1], (hu j).2⟩
  have hva : ∀ a, |v a| ≤ 2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1], (hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
  let R := μ.prod (tensorRootTreeLaw I degree n b
    (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
    (tensorPathProfile I degree n treeDegree h 0))
  have hc := tensorPerturbation_minimum_coordinates μ eig c I t n b h u v hu hv hmin
  have hgv (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) R ≤ L / N := by
    exact hvar N hN μ hμ hμinv m eig c K hK heig I u hua (Function.update v a w)
      (update_abs_le_two hva a hw) t ht n b hb h hh h0 H hH
  have hd := tensorDiagonal_fluctuation_at_minimum hNp μ eig c I degree amplitude n b treeDegree h
    hh h0 hb v t a (v a) L (hv a) he hs (fun w hw => (hgv w hw).1) (fun w hw => (hgv w hw).2) (by
      dsimp only
      intro w hw
      simpa only [M, tensorPerturbationPressureMean, Function.update_eq_self] using hc.2 a w hw)
  have hd' : tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amplitude n b treeDegree h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - diagonalMinimumCenter N (v a)|) ≤
      diagonalContactRate N L := by
    simpa only [Function.update_eq_self, diagonalMinimumCenter] using hd
  rw [tensorNamespacedArrayLaw_spectralDiagonal]
  exact (tensorSpectralDiagonal_clipping μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
    n b treeDegree h a (diagonalMinimumCenter N (v a))).trans hd'

end InvariantIsing

end

end OAI
