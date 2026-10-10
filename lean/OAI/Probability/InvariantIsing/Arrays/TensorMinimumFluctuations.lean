import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalMinimum
import OAI.Probability.InvariantIsing.Arrays.TensorObservableAverageLaw
import OAI.Probability.InvariantIsing.Arrays.PerturbationMinimumRates

namespace OAI

/-! Actual full-model diagonal fluctuations at coordinate pressure minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorDiagonal_fluctuation_at_minimum {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
    (hw : w ∈ Set.Icc (1 : ℝ) 2) (he : perturbationScale N ≤ 1 / 32)
    (hs : contactStep N ≤ 1 / 4)
    (hF : ∀ q : ℝ, |q| ≤ 2 →
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) 2 (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ q : ℝ, |q| ≤ 2 →
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ L / N)
    (hmin :
      let R := μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))
      let M := fun q => ∫ p, tensorDisorderPressure
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t) c I degree amplitude n p ∂ R
      ∀ q ∈ Set.Icc (1 : ℝ) 2, -M w + (w - 3 / 2) ^ 2 ≤ -M q + (q - 3 / 2) ^ 2) :
    let A := N * perturbationScale N
    let center := 2 * (N / A ^ 2) * (A * w - A * (3 / 2))
    tensorNamespacedObservableAverage μ
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|) ≤
      diagonalContactRate N L := by
  intro A center
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < 1 / (Real.sqrt N * perturbationScale N) :=
    one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr hn) he')
  have hE := tensorDiagonal_energy_at_minimum hN μ eig c I degree amplitude n b r h hh h0 hb v t a
    w (contactStep N) (1 / (Real.sqrt N * perturbationScale N)) (L / N) hw he hs' hs hθ hF hv hmin
  have ht := tensorFrozenDiagonal_observableAverage hN μ eig c I degree amplitude n b r h hh h0 v t a w
    (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|)
  rw [← ht]
  exact hE.2

end InvariantIsing

end

end OAI
