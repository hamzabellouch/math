import OAI.Probability.InvariantIsing.Magnetic.RestrictedRootShift
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairOrder

namespace OAI

/-! The actual constrained block overlap levels form an admissible path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal BigOperators

namespace InvariantIsing

lemma restrictedBlockPairMean_eq_average {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) :
    restrictedBlockPairMean hN S hS h b i = (N : ℝ)⁻¹ * ∑ j,
      ∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
        (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
        ∂Measure.pi (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0))) := by
  rw [restrictedBlockPairMean, integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold restrictedLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  rfl

lemma restrictedBlockPairMean_mem_unit {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : restrictedBlockPairMean hN S hS h b i ∈ Icc (0 : ℝ) 1 := by
  rw [restrictedBlockPairMean_eq_average]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi (j : Fin N) : (∫ z,
      restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
        (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
        ∂Measure.pi (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0)))) ∈
      Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg (fun z => restrictedPairCoordinateMean_nonneg hN S hS _ _ _ _ i j z)
    · calc
        _ ≤ ∫ _z, (1 : ℝ) ∂Measure.pi
            (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0))) :=
          integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
            (integrable_const _) (fun z => (le_abs_self _).trans
              (restrictedPairCoordinateMean_bound hN S hS _ _ _ _ i j z))
        _ = 1 := by simp
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le) (Finset.sum_nonneg (fun j _ => (hi j).1))
  · calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hi j).2)) (inv_nonneg.mpr hn.le)
      _ = 1 := by simp [hn.ne']

lemma restrictedBlockPairMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    Monotone (restrictedBlockPairMean hN S hS h b) := by
  intro i k hik
  rw [restrictedBlockPairMean_eq_average, restrictedBlockPairMean_eq_average]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
    (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ k j _)
    (fun z => restrictedPairCoordinateMean_monotone hN S hS _ _ _ _ j z hik)

def restrictedBlockOverlapPath {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) : OverlapPath :=
  fieldLevelPath h (restrictedBlockPairMean hN S hS h (fun _ => 0))
    (restrictedBlockPairMean_monotone hN S hS h _)
    (restrictedBlockPairMean_mem_unit hN S hS h _)

end InvariantIsing

end

end OAI
