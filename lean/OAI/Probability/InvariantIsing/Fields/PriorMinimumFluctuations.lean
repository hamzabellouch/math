import OAI.Probability.InvariantIsing.Fields.PriorDiagonalMinimum
import OAI.Probability.InvariantIsing.Fields.PriorReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.PerturbationMinimumRates

namespace OAI

/-! Vanishing self-overlap fluctuation in the actual constrained-prior Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma sqrt_dimension_mul {N : ℕ} (hN : 0<N) (L : ℝ) :
    Real.sqrt (N*L) = N*Real.sqrt (L/N) := by
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (N : ℝ)*L=(N : ℝ)^2*(L/N) := by field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)]

theorem priorDiagonal_fluctuation_at_minimum {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/32) (hs : contactStep N≤1/4)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (priorNamespacedLog ν₀ (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i)) 2 (μ.prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (priorNamespacedLog ν₀ (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i)) (μ.prod gaussianCoordinates)≤N*L)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, priorNamespacedLog ν₀
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2, -M w+(w-3/2)^2≤-M q+(q-3/2)^2) :
    let A := N*perturbationScale N
    let center := 2*(N/A^2)*(A*w-A*(3/2))
    priorNamespacedObservableAverage μ ν₀
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-center|)≤diagonalContactRate N L := by
  intro A center
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < 1 / (Real.sqrt N * perturbationScale N) :=
    one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr hn) he')
  have hE := priorDiagonal_energy_at_minimum hN μ ν₀ eig c I degree amplitude r h hh h0 v t a
    w (contactStep N) (1 / (Real.sqrt N * perturbationScale N)) (N * L) hw he hs' hs hθ hF hv hmin
  have ht := priorFrozenDiagonal_observableAverage hN μ ν₀ eig c I degree amplitude r h hh h0 v t a w
    (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|)
  rw [← ht]
  simpa only [sqrt_dimension_mul hN L,center,A,diagonalContactRate,mul_assoc] using hE.2

end InvariantIsing

end

end OAI
