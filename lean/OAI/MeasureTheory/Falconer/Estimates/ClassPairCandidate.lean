import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Radial.RadialFailureMass

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def classPairMask (Q : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ℝ≥0∞ :=
  let c := outerEntry m₁ m₂ N β
  ENNReal.ofReal (outerEndpointMask Q ρ m₁ N lam sig kap c z.1 (sourceRadialUnit z.1 z.2)*
    outerEndpointMask Q ν m₂ N lam sig kap c z.2 (sourceRadialUnit z.1 z.2))

@[fun_prop] theorem measurable_classPairMask (Q : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    Measurable (classPairMask Q ρ ν m₁ m₂ N lam sig kap β) := by
  change Measurable (fun z : Plane × Plane => ENNReal.ofReal
    (outerEndpointMask Q ρ m₁ N lam sig kap (outerEntry m₁ m₂ N β) z.1 (sourceRadialUnit z.1 z.2)*
      outerEndpointMask Q ν m₂ N lam sig kap (outerEntry m₁ m₂ N β) z.2 (sourceRadialUnit z.1 z.2)))
  apply Measurable.ennreal_ofReal
  apply Measurable.mul
  · exact (measurable_outerEndpointMask Q ρ m₁ N lam sig kap (outerEntry m₁ m₂ N β)).comp
      (f := fun z : Plane × Plane => (z.1, sourceRadialUnit z.1 z.2))
      (measurable_fst.prodMk measurable_sourceRadialUnit_joint)
  · exact (measurable_outerEndpointMask Q ν m₂ N lam sig kap (outerEntry m₁ m₂ N β)).comp
      (f := fun z : Plane × Plane => (z.2, sourceRadialUnit z.1 z.2))
      (measurable_snd.prodMk measurable_sourceRadialUnit_joint)

theorem classPairMask_le_one (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    classPairMask Q ρ ν m₁ m₂ N lam sig kap β z ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  have h₁ := outerEndpointMask_bounds Q hQ ρ m₁ N lam sig kap (outerEntry m₁ m₂ N β) z.1 (sourceRadialUnit z.1 z.2)
  have h₂ := outerEndpointMask_bounds Q hQ ν m₂ N lam sig kap (outerEntry m₁ m₂ N β) z.2 (sourceRadialUnit z.1 z.2)
  nlinarith

noncomputable def classPairCandidate (Q : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((ρ.prod ν).withDensity (fun z => distanceWeight z*classPairMask Q ρ ν m₁ m₂ N lam sig kap β z)).map
    (fun z => dist z.1 z.2)

noncomputable def classPairRemoved (Q : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((ρ.prod ν).withDensity (fun z => distanceWeight z*(1-classPairMask Q ρ ν m₁ m₂ N lam sig kap β z))).map
    (fun z => dist z.1 z.2)

theorem classPairCandidate_decomposition (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    weightedDistance (ρ.prod ν) = classPairCandidate Q ρ ν m₁ m₂ N lam sig kap β+
      classPairRemoved Q ρ ν m₁ m₂ N lam sig kap β := by
  exact masked_pushforward_decomposition (ρ.prod ν) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (classPairMask Q ρ ν m₁ m₂ N lam sig kap β) (by unfold distanceWeight; fun_prop)
    (measurable_classPairMask _ _ _ _ _ _ _ _ _ _) (classPairMask_le_one Q hQ _ _ _ _ _ _ _ _ _)

theorem classPairCandidate_finite (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ ν : Measure Plane)
    [IsFiniteMeasure ((ρ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    IsFiniteMeasure (classPairCandidate Q ρ ν m₁ m₂ N lam sig kap β) ∧
      IsFiniteMeasure (classPairRemoved Q ρ ν m₁ m₂ N lam sig kap β) :=
  finite_summands _ _ _ (classPairCandidate_decomposition Q hQ ρ ν m₁ m₂ N lam sig kap β)

theorem classPairCandidate_totalVariation (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ ν : Measure Plane)
    [IsFiniteMeasure ((ρ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    let h := classPairCandidate_finite Q hQ ρ ν m₁ m₂ N lam sig kap β
    letI := h.1
    letI := h.2
    ((weightedDistance (ρ.prod ν)).toSignedMeasure-
      (classPairCandidate Q ρ ν m₁ m₂ N lam sig kap β).toSignedMeasure).totalVariation =
      classPairRemoved Q ρ ν m₁ m₂ N lam sig kap β := by
  let := (classPairCandidate_finite Q hQ ρ ν m₁ m₂ N lam sig kap β).1
  let := (classPairCandidate_finite Q hQ ρ ν m₁ m₂ N lam sig kap β).2
  exact totalVariation_sub_of_add _ _ _ (classPairCandidate_decomposition Q hQ ρ ν m₁ m₂ N lam sig kap β)

end PlanarFalconer

end OAI
