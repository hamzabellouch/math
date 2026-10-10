import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockOverlap

namespace OAI

/-! Coordinate overlap paths for the actual constrained scalar-field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def restrictedCoordinatePairMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (j : Fin N) (i : Fin (h.depth+1)) : ℝ :=
  ∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
    (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
    ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))

lemma restrictedCoordinatePairMean_mem_unit {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N)
    (i : Fin (h.depth+1)) : restrictedCoordinatePairMean hN S hS h j i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun z => restrictedPairCoordinateMean_nonneg hN S hS _ _ _ _ i j z)
  · calc
      _ ≤ ∫ _z, (1 : ℝ) ∂(vectorGaussianLaw N
          (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) :=
        integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
          (integrable_const _) (fun z => (le_abs_self _).trans
            (restrictedPairCoordinateMean_bound hN S hS _ _ _ _ i j z))
      _ = 1 := by simp

lemma restrictedCoordinatePairMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N) :
    Monotone (restrictedCoordinatePairMean hN S hS h j) := by
  intro i k hik
  exact integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
    (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ k j _)
    (fun z => restrictedPairCoordinateMean_monotone hN S hS _ _ _ _ j z hik)

def restrictedCoordinateOverlapPath {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N) : OverlapPath :=
  fieldLevelPath h (restrictedCoordinatePairMean hN S hS h j)
    (restrictedCoordinatePairMean_monotone hN S hS h j)
    (restrictedCoordinatePairMean_mem_unit hN S hS h j)

lemma restrictedBlockOverlapPath_eq_average {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (t : ℝ) :
    restrictedBlockOverlapPath hN S hS h t =
      (N : ℝ)⁻¹ * ∑ j, restrictedCoordinateOverlapPath hN S hS h j t := by
  change restrictedBlockPairMean hN S hS h (fun _ => 0) (fieldLevelIndex h t) = _
  rw [restrictedBlockPairMean_eq_average]
  rfl

end InvariantIsing

end

end OAI
