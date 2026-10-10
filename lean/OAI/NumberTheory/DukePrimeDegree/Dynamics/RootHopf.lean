import OAI.NumberTheory.DukePrimeDegree.Geometry.RootContraction

namespace OAI

/-!
# The Hopf principle in an actual root box

A diagonal-invariant integrable observable is constant on almost every
conditional root fiber whenever the diagonal direction has root weight
one. The proof uses the actual root-box measure and its disintegration.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Stable root fibers carry constant values of invariant observables. -/
theorem ae_rootBox_eq_of_diagonal_invariant
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hweight : ell i - ell j = 1)
    (μ : Measure (X n)) [IsFiniteMeasure μ] [μ.Regular]
    (B : RootBox hij k)
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    (f : X n → ℝ) (hf : Integrable f μ)
    (hfinv : (fun x => f (rightAction x (diagonalOneParameter ell hell 1))) =ᵐ[μ] f) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ᵐ t ∂B.conditionalKernel μ z.1,
      f (rootQuotientParametrization hij z) =
        f (rootQuotientParametrization hij (z.1, t)) := by
  let : MetricSpace (X n) := TopologicalSpace.metrizableSpaceMetric (X n)
  let := rootTranslationAction hij
  let : ContinuousSMul (Multiplicative ℝ) (X n) := rootTranslationAction_continuous hij
  let R := rootQuotientParametrization (k := k) hij
  have hR : Measurable R := (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
  have hRμ : (B.coordinateMeasure μ).map R ≤ μ := by
    rw [B.map_coordinateMeasure μ]
    exact Measure.restrict_le_self
  let a : ℕ → ((RootSlice i j k × ℝ) × ℝ) → Multiplicative ℝ := fun m z =>
    Multiplicative.ofAdd (Real.exp ((ell j - ell i) * (m : ℝ)) * (z.2 - z.1.2))
  have ha : ∀ᵐ z ∂conditionalPairMeasure (B.coordinateMeasure μ),
      Tendsto (fun m => a m z) atTop (𝓝 1) := by
    apply ae_of_all
    intro z
    exact root_parameter_contracts ell hweight (z.2 - z.1.2)
  have hp : ∀ᵐ z ∂conditionalPairMeasure (B.coordinateMeasure μ), ∀ m,
      (fun x => rightAction x (diagonalOneParameter ell hell 1))^[m] (R (z.1.1, z.2)) =
        a m z • (fun x => rightAction x (diagonalOneParameter ell hell 1))^[m] (R z.1) := by
    apply ae_of_all
    intro z m
    rw [diagonal_right_iterate, diagonal_right_iterate]
    change rightAction (R (z.1.1, z.2)) (diagonalOneParameter ell hell (m : ℝ)) =
      rightAction (rightAction (R z.1) (diagonalOneParameter ell hell (m : ℝ)))
        (Matrix.SpecialLinearGroup.transvection hij
          (Real.exp ((ell j - ell i) * (m : ℝ)) * (z.2 - z.1.2)))
    have he : R (z.1.1, z.2) = rightAction (R z.1)
        (Matrix.SpecialLinearGroup.transvection hij (z.2 - z.1.2)) := by
      have ht : z.1.2 + (z.2 - z.1.2) = z.2 := by ring
      simpa only [R, ht] using
        rootQuotientParametrization_add hij z.1.1 z.1.2 (z.2 - z.1.2)
    rw [he, root_pair_diagonal_translate hij ell hell]
  exact ae_conditional_eq_of_contracting_orbits μ (B.coordinateMeasure μ)
    R hR hRμ _ hT a ha hp f hf hfinv

end DukePrimeDegree

end

end OAI
