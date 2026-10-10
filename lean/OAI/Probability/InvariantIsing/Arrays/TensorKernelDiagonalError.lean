import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalError

namespace OAI

/-! The finite cascade top level is retained in each tensor diagonal center. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma finiteTreeDiagonal_mem (n : ℕ) : (n : ℝ) / (n + 1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.zero_lt_succ n
  refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).mpr ?_⟩
  exact_mod_cast Nat.le_succ n

lemma tensorKernel_diagonal_deviation {N m : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (center : Fin m → ℝ) (x : Spin N × LabeledLeaf n) :
    |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I d n r U x x -
      (∏ a, spectralDiagonalCenter (center a) ^ d a) * ((n : ℝ) / (n + 1 : ℕ)) ^ r| =
      |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
        ∏ a, spectralDiagonalCenter (center a) ^ d a| * ((n : ℝ) / (n + 1 : ℕ)) ^ r := by
  rw [spectralPerturbationKernel, treeOverlap_self, ← sub_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (finiteTreeDiagonal_mem n).1 r)]
  rfl

theorem tensorKernelDiagonalError_le {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (d : Fin m → ℕ) (treeDegree : ℕ) (center : Fin m → ℝ) :
    tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N)
        I d n treeDegree U x x -
        (∏ a, spectralDiagonalCenter (center a) ^ d a) * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree|) ≤
      ∑ a, (d a : ℝ) * tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) := by
  let Z := tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
    (fun U x => |(∏ a, projectedOverlap (specialRotation U) (I a) x.1 x.1 ^ d a) -
      ∏ a, spectralDiagonalCenter (center a) ^ d a|)
  have hZ : 0 ≤ Z := integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  have he : tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N)
        I d n treeDegree U x x -
        (∏ a, spectralDiagonalCenter (center a) ^ d a) * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree|) =
      Z * ((n : ℝ) / (n + 1 : ℕ)) ^ treeDegree := by
    unfold tensorNamespacedObservableAverage Z
    simp_rw [tensorKernel_diagonal_deviation, integral_mul_const]
    rfl
  rw [he]
  exact (mul_le_of_le_one_right hZ (pow_le_one₀ (finiteTreeDiagonal_mem n).1 (finiteTreeDiagonal_mem n).2)).trans
    (tensorMonomialDiagonalError_le μ eig c I degree amplitude n b r h d center)

end InvariantIsing

end

end OAI
