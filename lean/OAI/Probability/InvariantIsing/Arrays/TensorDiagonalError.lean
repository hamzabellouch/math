import OAI.Probability.InvariantIsing.Arrays.TensorObservableAverageLaw

namespace OAI

/-! The actual full-model monomial diagonal error is controlled coordinate by coordinate. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_spectralDiagonalDeviation {N : ℕ} (I : Finset (Fin N)) (n : ℕ) (b : ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (Spin N × LabeledLeaf n) =>
      |projectedOverlap (specialRotation p.1) I p.2.1 p.2.1 - b|) := by
  apply measurable_from_prod_countable_left
  intro x
  exact ((measurable_projectedOverlap I x.1 x.1).sub_const b).abs

lemma spectralDiagonalDeviation_abs_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (b : ℝ) (σ : Spin N) :
    abs (abs (projectedOverlap U I σ σ - b)) ≤ 1 + |b| := by
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (projectedOverlap_abs_le_one _ _ _ _) le_rfl)

theorem tensorMonomialDiagonalError_le {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (d : Fin m → ℕ) (center : Fin m → ℝ) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
        ∏ a, spectralDiagonalCenter (center a) ^ d a|) ≤
      ∑ a, (d a : ℝ) * tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) := by
  let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := tensorNamespacedReference eig c I degree amplitude n r h
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
  have hiE (a : Fin m) : Integrable (fun p : TensorFlatDisorder N n => ∫ x, E a p.1.1 x ∂ν p) P :=
    tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h (E a) (hE a) (hEb a)
  have hiD : Integrable (fun p : TensorFlatDisorder N n => ∫ x, D p.1.1 x ∂ν p) P :=
    tensorNamespacedObservableAverage_integrable μ eig c I degree amplitude n b r h D hD hDb
  have hiS : Integrable (fun p : TensorFlatDisorder N n =>
      ∑ a, (d a : ℝ) * ∫ x, E a p.1.1 x ∂ν p) P :=
    integrable_finsetSum _ (fun a _ => (hiE a).const_mul (d a : ℝ))
  change (∫ p, ∫ x, D p.1.1 x ∂ν p ∂P) ≤
    ∑ a, (d a : ℝ) * ∫ p, ∫ x, E a p.1.1 x ∂ν p ∂P
  calc
    _ ≤ ∫ p : TensorFlatDisorder N n, ∑ a, (d a : ℝ) * ∫ x, E a p.1.1 x ∂ν p ∂P := by
      apply integral_mono hiD hiS
      intro p
      have hiD' : Integrable (D p.1.1) (ν p) :=
        Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable _ (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using hDb p.1.1 x)
      have hiE' (a : Fin m) : Integrable (E a p.1.1) (ν p) :=
        Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable _ (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs] using hEb a p.1.1 x)
      calc
        _ ≤ ∫ x, ∑ a, (d a : ℝ) * E a p.1.1 x ∂ν p :=
          integral_mono hiD' (integrable_finsetSum _ (fun a _ => (hiE' a).const_mul _)) (hle p.1.1)
        _ = _ := by rw [integral_finsetSum _ (fun a _ => (hiE' a).const_mul _)]; simp_rw [integral_const_mul]
    _ = _ := by rw [integral_finsetSum _ (fun a _ => (hiE a).const_mul _)]; simp_rw [integral_const_mul]

end InvariantIsing

end

end OAI
