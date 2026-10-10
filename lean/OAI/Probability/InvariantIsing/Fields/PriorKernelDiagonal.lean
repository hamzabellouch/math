import OAI.Probability.InvariantIsing.Fields.PriorReplicaAverage
import OAI.Probability.InvariantIsing.Arrays.TensorKernelDiagonalError

namespace OAI

/-! Coordinate deviations control the selected kernel for constrained priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem priorMonomialDiagonalError_le {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ)
    (d : Fin m → ℕ) (center : Fin m → ℝ) :
    priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
        ∏ a, spectralDiagonalCenter (center a) ^ d a|) ≤
      ∑ a, (d a : ℝ) * priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) := by
  let P := μ.prod gaussianCoordinates
  let ν := priorNamespacedReference ν₀ eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i)
  let D := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) =>
    |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
      ∏ a, spectralDiagonalCenter (center a) ^ d a|
  let E := fun (a : Fin m) (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) =>
    |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|
  let C := fun a => 1 + |center a|
  have hE (a : Fin m) : Measurable (Function.uncurry (E a)) :=
    measurable_spectralDiagonalDeviation (I a) n (center a)
  have hD : Measurable (Function.uncurry D) := by
    apply measurable_from_prod_countable_left
    intro x
    exact ((Finset.measurable_prod _ fun a _ =>
      (measurable_projectedOverlap (I a) x.1 x.1).pow_const (d a)).sub_const _).abs
  have hEb (a : Fin m) (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) : |E a U x| ≤ C a :=
    spectralDiagonalDeviation_abs_le (specialRotation U) (I a) (center a) x.1
  have hle (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) :
      D U x ≤ ∑ a, (d a : ℝ) * E a U x :=
    spectralMonomial_clipped_self_deviation_le (specialRotation U) I d center x.1
  have hDb (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) :
      |D U x| ≤ ∑ a, (d a : ℝ) * C a := by
    rw [abs_of_nonneg (abs_nonneg _)]
    exact (hle U x).trans (Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hEb a U x)) (Nat.cast_nonneg _))
  have hiE (a : Fin m) : Integrable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, E a p.1 x ∂ν p) P :=
    priorNamespacedObservableAverage_integrable μ ν₀ eig c I degree amplitude r h (E a) (hE a) (hEb a)
  have hiD : Integrable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => ∫ x, D p.1 x ∂ν p) P :=
    priorNamespacedObservableAverage_integrable μ ν₀ eig c I degree amplitude r h D hD hDb
  have hiS : Integrable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      ∑ a, (d a : ℝ) * ∫ x, E a p.1 x ∂ν p) P :=
    integrable_finsetSum _ (fun a _ => (hiE a).const_mul (d a : ℝ))
  change (∫ p, ∫ x, D p.1 x ∂ν p ∂P) ≤
    ∑ a, (d a : ℝ) * ∫ p, ∫ x, E a p.1 x ∂ν p ∂P
  calc
    _ ≤ ∫ p : SpecialOrthogonal N × (ℕ → ℝ), ∑ a, (d a : ℝ) * ∫ x, E a p.1 x ∂ν p ∂P := by
      apply integral_mono hiD hiS
      intro p
      have hiD' : Integrable (D p.1) (ν p) :=
        Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable _ (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using hDb p.1 x)
      have hiE' (a : Fin m) : Integrable (E a p.1) (ν p) :=
        Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable _ (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using hEb a p.1 x)
      calc
        _ ≤ ∫ x, ∑ a, (d a : ℝ) * E a p.1 x ∂ν p :=
          integral_mono hiD' (integrable_finsetSum _ (fun a _ => (hiE' a).const_mul _)) (hle p.1)
        _ = _ := by rw [integral_finsetSum _ (fun a _ => (hiE' a).const_mul _)]; simp_rw [integral_const_mul]
    _ = _ := by rw [integral_finsetSum _ (fun a _ => (hiE a).const_mul _)]; simp_rw [integral_const_mul]


theorem priorKernelDiagonalError_le {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ)
    (d : Fin m → ℕ) (treeDegree : ℕ) (center : Fin m → ℝ) :
    priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N)
        I d n treeDegree U x x -
        (∏ a, spectralDiagonalCenter (center a) ^ d a) * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree|) ≤
      ∑ a, (d a : ℝ) * priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) := by
  let Z := priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
    (fun U x => |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
      ∏ a, spectralDiagonalCenter (center a) ^ d a|)
  have hZ : 0 ≤ Z := integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  have he : priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N)
        I d n treeDegree U x x -
        (∏ a, spectralDiagonalCenter (center a) ^ d a) * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree|) =
      Z * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree := by
    unfold priorNamespacedObservableAverage Z
    simp_rw [tensorKernel_diagonal_deviation, integral_mul_const]
    rfl
  rw [he]
  exact (mul_le_of_le_one_right hZ (pow_le_one₀ (finiteTreeDiagonal_mem n).1 (finiteTreeDiagonal_mem n).2)).trans
    (priorMonomialDiagonalError_le μ ν₀ eig c I degree amplitude r h d center)

end InvariantIsing

end

end OAI
