import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenFluctuation
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationVariance

namespace OAI

/-! The actual finite perturbation has the CGF concentration needed at minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The selected field's mean is an actual pressure difference, and its
centered fluctuation is uniformly of order square root volume. -/
theorem tensorPerturbationCGF_statistics (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin N → Fin m → ℕ,
    ∀ u : Fin N → ℝ, (∀ j, |u j| ≤ 2) →
    ∀ D : ℝ, 0 ≤ D → (∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) →
    ∀ n : ℕ, ∀ r : Fin N → ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
    ∀ j : Fin N, ∀ w : ℝ, |w| ≤ 2 →
      let v := tensorPathProfile I degree n r h
      let R := μ.prod (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0))
      let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
      let M := fun a => ∫ p, tensorDisorderPressure eig c I degree
        (tensorPerturbationAmplitude N (Function.update u j a)) n p ∂ R
      let Z := tensorFrozenCGF eig c I degree (tensorPerturbationAmplitude N u) n r h j
        (perturbationAmplitude N j * w)
      MemLp Z 2 Q ∧ (∫ p, Z p ∂Q) = N * (M w - M 0) ∧
        (∫ p, |Z p - ∫ p', Z p' ∂Q| ∂Q) ≤
          2 * N * Real.sqrt ((4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
            ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 8 * D) ^ 2) / N) := by
  obtain ⟨C, hC, hv⟩ := tensorPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I degree u hu D hD hdegree n r b hb h hh h0 H hH
    j w hw v R Q M Z
  let : IsProbabilityMeasure μ := hμ
  have hNm : 0 < N := by omega
  let a := perturbationAmplitude N j
  let B := (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
    ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 8 * D) ^ 2) / N
  have hdata (s : ℝ) (hs : |s| ≤ 2) :
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update (tensorPerturbationAmplitude N u) j (a * s)) n) 2 R ∧
      variance (tensorDisorderPressure eig c I degree
        (Function.update (tensorPerturbationAmplitude N u) j (a * s)) n) R ≤ B := by
    simpa only [tensorPerturbationAmplitude_update] using
      hv N hN μ hμ hμinv m eig c K hK heig I degree (Function.update u j s)
        (update_abs_le_two hu j hs) D hD hdegree n r b hb h hh h0 H hH
  have hF : ∀ s : ℝ, s = a * w ∨ s = 0 →
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update (tensorPerturbationAmplitude N u) j s) n) 2 R := by
    intro s hs
    rcases hs with rfl | rfl
    · exact (hdata w hw).1
    · simpa only [mul_zero] using (hdata 0 (by norm_num)).1
  have hvar : ∀ s : ℝ, s = a * w ∨ s = 0 →
      variance (tensorDisorderPressure eig c I degree
        (Function.update (tensorPerturbationAmplitude N u) j s) n) R ≤ B := by
    intro s hs
    rcases hs with rfl | rfl
    · exact (hdata w hw).2
    · simpa only [mul_zero] using (hdata 0 (by norm_num)).2
  have hc := tensorFrozenCGF_centered_L1_bound hNm μ eig c I degree
    (tensorPerturbationAmplitude N u) n b r h hh h0 hb j (a * w) B hF hvar
  have hm := tensorFrozenCGF_mean hNm μ eig c I degree
    (tensorPerturbationAmplitude N u) n b r h hh h0 hb j (a * w) hF
  refine ⟨hc.1, ?_, hc.2⟩
  simpa only [M, tensorPerturbationAmplitude_update, mul_zero] using hm

end InvariantIsing

end

end OAI
