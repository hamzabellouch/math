import OAI.Probability.InvariantIsing.Fields.SpinPriorDiagonalMinimum
import OAI.Probability.InvariantIsing.Fields.SpinPriorObservableAverageLaw
import OAI.Probability.InvariantIsing.Fields.PriorMinimumFluctuations
import OAI.Probability.InvariantIsing.Arrays.PerturbationMinimumRates

namespace OAI

/-! Vanishing self-overlap fluctuation in the actual constrained-prior Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorDiagonal_fluctuation_at_minimum {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/32) (hs : contactStep N≤1/4)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2, -M w+(w-3/2)^2≤-M q+(q-3/2)^2) :
    let A := N*perturbationScale N
    let center := 2*(N/A^2)*(A*w-A*(3/2))
    spinPriorObservableAverage (n := n) μ π
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-center|)≤diagonalContactRate N L := by
  intro A center
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < 1 / (Real.sqrt N * perturbationScale N) :=
    one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr hn) he')
  have hE := spinPriorDiagonal_energy_at_minimum hN μ π b eig c I degree amplitude r h hh h0 v t a
    w (contactStep N) (1 / (Real.sqrt N * perturbationScale N)) (N * L) hw he hs' hs hθ hF hv hmin
  have ht := spinPriorFrozenDiagonal_observableAverage hN μ π eig c I degree amplitude n b r h hh h0 v t a w
    (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|)
  rw [← ht]
  simpa only [sqrt_dimension_mul hN L,center,A,diagonalContactRate,mul_assoc] using hE.2

end InvariantIsing

end

end OAI
