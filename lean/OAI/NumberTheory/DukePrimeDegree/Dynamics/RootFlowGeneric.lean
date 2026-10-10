import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnitFlowSmoothing
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootContraction
import OAI.NumberTheory.PrimePackets.ErgodicDecomposition

namespace OAI

/-!
# Generic sets for the actual root flow

The action used here is the actual right transvection action on the
integer-lattice quotient. Its invariant probability has an ergodic
decomposition for the entire real flow. On each such ergodic component,
the uniform generic-set theorem uses no chosen-time ergodicity premise.
The further homogeneous-support conclusion is not asserted here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree
open PrimeDegreePackets

theorem root_flow_ergodic_decomposition {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hroot : ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ) :
    let := rootTranslationAction hij
    ∃ (m : MeasurableSpace (X n)) (hm : m ≤ xMeasurableSpace n),
      letI : MeasurableSpace (X n) := xMeasurableSpace n
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
        ∀ᵐ z ∂μ.trim hm, ErgodicSMul (Multiplicative ℝ) (X n) (condExpKernel μ m z) := by
  let := rootTranslationAction hij
  let : ContinuousSMul (Multiplicative ℝ) (X n) := rootTranslationAction_continuous hij
  apply continuous_action_ergodic_decomposition μ
  intro t
  exact ⟨(continuous_rightAction _).measurable, hroot t.toAdd⟩

/-- Uniform generic sets on an actual root-flow ergodic component. -/
theorem exists_uniform_root_flow_generic_set {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ν : Measure (X n)) [IsProbabilityMeasure ν]
    (herg : let := rootTranslationAction hij
      ErgodicSMul (Multiplicative ℝ) (X n) ν)
    (f : X n →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set (X n), MeasurableSet G ∧ ν Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀,
        |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ),
            f (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) -
          ∫ y, f y ∂ν| ≤ ε := by
  let := rootTranslationAction hij
  let : ContinuousSMul (Multiplicative ℝ) (X n) := rootTranslationAction_continuous hij
  let : ErgodicSMul (Multiplicative ℝ) (X n) ν := herg
  have hact (t : ℝ) (x : X n) : realActionTime t x =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := rfl
  simpa only [hact] using
    exists_uniform_integer_flow_generic_set ν f ε δ hε hδ

end DukePrimeDegree

end

end OAI
