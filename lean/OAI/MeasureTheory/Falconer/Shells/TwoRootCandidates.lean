import OAI.MeasureTheory.Falconer.Shells.TwoRootMasks
import OAI.MeasureTheory.Falconer.Shells.RestoredShellCandidates

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def restoredTwoRootCandidate (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z)).map
    (fun z => dist z.1 z.2)

noncomputable def restoredTwoRootRemoved (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*(1-restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z))).map
    (fun z => dist z.1 z.2)

theorem restoredTwoRootCandidate_decomposition (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    weightedDistance (μ.prod ν) = restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β+
      restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  exact masked_pushforward_decomposition (μ.prod ν) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) (by unfold distanceWeight; fun_prop)
    (measurable_restoredTwoRootMask ..)
    (fun z => restoredTwoRootMask_le_one Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z)

theorem restoredTwoRootCandidate_finite (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    IsFiniteMeasure (restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) ∧
      IsFiniteMeasure (restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β) :=
  finite_summands _ _ _ (restoredTwoRootCandidate_decomposition Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

theorem restoredTwoRootCandidate_totalVariation (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    let h := restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β
    letI := h.1
    letI := h.2
    ((weightedDistance (μ.prod ν)).toSignedMeasure-
      (restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).toSignedMeasure).totalVariation =
      restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  let := (restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).1
  let := (restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).2
  exact totalVariation_sub_of_add _ _ _ (restoredTwoRootCandidate_decomposition Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

end PlanarFalconer

end OAI
