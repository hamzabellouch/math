import OAI.Probability.InvariantIsing.Arrays.TensorMinimumFluctuations
import OAI.Probability.InvariantIsing.Arrays.TensorGGMinimum
import OAI.Probability.InvariantIsing.Arrays.FullPerturbationVariance

namespace OAI

/-! For the complete perturbation, both coordinate minima force the
Ghirlanda–Guerra errors to vanish. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorPerturbationPressureMean {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) : ℝ :=
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
  ∫ p, tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
    (tensorPerturbationAmplitude N u) n p
    ∂(μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0)))

def diagonalMinimumCenter (N : ℕ) (w : ℝ) : ℝ :=
  let a := N * perturbationScale N
  2 * (N / a ^ 2) * (a * w - a * (3 / 2))

/-- For the manuscript's full finite perturbation, genuine pressure-coordinate
minima give a GG residual bounded by two explicit rates tending to zero. -/
theorem fullPerturbationPressure_minimumGG (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t| ≤ 1 →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let M := tensorPerturbationPressureMean μ eig c I (n := n) (b := b) (h := h)
      let degree := fun j : Fin N => enumeratedSpectralDegree m j
      let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
        ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
      perturbationScale N ≤ 1 / 32 → contactStep N ≤ 1 / 4 →
      (∀ (j : Fin N) (w : ℝ), w ∈ Set.Icc (1 : ℝ) 2 →
        -M u v t + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
        -M (Function.update u j w) v t + perturbationWeight j * (w - 3 / 2) ^ 2) →
      (∀ (a : Fin m) (w : ℝ), w ∈ Set.Icc (1 : ℝ) 2 →
        -M u v t + (v a - 3 / 2) ^ 2 ≤ -M u (Function.update v a w) t + (w - 3 / 2) ^ 2) →
      ∀ j : Fin N, ∀ q : ℕ, ∀ B : ℝ, 0 ≤ B →
      ∀ D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ,
      Measurable (Function.uncurry D) → (∀ U σ, |D U σ| ≤ B) →
      |tensorSpectralGGResidual μ (diagonalPerturbedEigenvalues eig I v t) c I degree
        (tensorPerturbationAmplitude N u) n b treeDegree h j D| ≤
        contactGGRate N j L B +
          2 * B * (∑ a, (degree j a : ℝ)) * diagonalContactRate N L := by
  obtain ⟨C, hC, hvar⟩ := fullPerturbationPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I u hu v hv t ht n b hb h hh h0 H hH
    M degree treeDegree L he hs hminu hminv j q B hB D hD hDb
  let : IsProbabilityMeasure μ := hμ
  have hNp : 0 < N := by omega
  have hua : ∀ j, |u j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1], (hu j).2⟩
  have hva : ∀ a, |v a| ≤ 2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1], (hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  let R := μ.prod (tensorRootTreeLaw I degree n b
    (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
    (tensorPathProfile I degree n treeDegree h 0))
  have hgu (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (Function.update amplitude j (perturbationAmplitude N j * w)) n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
        (Function.update amplitude j (perturbationAmplitude N j * w)) n) R ≤ L / N := by
    simpa only [tensorPerturbationAmplitude_update] using
      hvar N hN μ hμ hμinv m eig c K hK heig I (Function.update u j w)
        (update_abs_le_two hua j hw) v hva t ht n b hb h hh h0 H hH
  have hgv (a : Fin m) (w : ℝ) (hw : |w| ≤ 2) :
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) 2 R ∧
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n) R ≤ L / N := by
    exact hvar N hN μ hμ hμinv m eig c K hK heig I u hua (Function.update v a w)
      (update_abs_le_two hva a hw) t ht n b hb h hh h0 H hH
  have hdiag (a : Fin m) : tensorNamespacedObservableAverage μ (diagonalPerturbedEigenvalues eig I v t)
      c I degree amplitude n b treeDegree h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - diagonalMinimumCenter N (v a)|) ≤
      diagonalContactRate N L := by
    have hd := tensorDiagonal_fluctuation_at_minimum hNp μ eig c I degree amplitude n b treeDegree h
      hh h0 hb v t a (v a) L (hv a) he hs (fun w hw => (hgv a w hw).1)
      (fun w hw => (hgv a w hw).2) (by
        dsimp only
        intro w hw
        simpa only [M, tensorPerturbationPressureMean, Function.update_eq_self] using hminv a w hw)
    simpa only [Function.update_eq_self, diagonalMinimumCenter] using hd
  have hgm : ∀ w ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
        n b treeDegree h j (u j) + perturbationWeight j * (u j - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ (diagonalPerturbedEigenvalues eig I v t) c I degree amplitude
        n b treeDegree h j w + perturbationWeight j * (w - 3 / 2) ^ 2 := by
    intro w hw
    simpa only [amplitude, M, tensorPerturbationPressureMean, tensorGaussianCoordinatePressure, ← tensorPerturbationAmplitude_update,
      Function.update_eq_self] using hminu j w hw
  have hg := tensorGaussianGG_at_minimum hNp μ (diagonalPerturbedEigenvalues eig I v t) c I degree
    amplitude n b treeDegree h hh h0 hb j (u j) L (hu j) (by linarith) hs rfl
    (fun w hw => (hgu w hw).1) (fun w hw => (hgu w hw).2) hgm B hB D hD hDb
    (fun a => diagonalMinimumCenter N (v a)) (fun _ => diagonalContactRate N L) hdiag
  simpa only [← Finset.sum_mul, mul_assoc] using hg

end InvariantIsing

end

end OAI
