import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnitFlowSmoothing
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootContraction

namespace OAI

/-!
# One generic set for the finite separating observables

The finite family needed to separate the compact set of limiting
shears uses one measurable good set and one common time threshold.
Only ergodicity of the actual full real-flow component is used.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_finite_uniform_integer_flow_generic_set
    {Y I : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    [Fintype I]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : I → Y →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ i, ∀ N ≥ N₀,
        |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f i (realActionTime t x)) -
          ∫ y, f i y ∂μ| ≤ ε := by
  classical
  let a : ℝ := δ / (Fintype.card I + 1)
  have ha : 0 < a := div_pos hδ (by positivity)
  choose G hG hGμ N₀ hN using
    fun i => exists_uniform_integer_flow_generic_set μ (f i) ε a hε ha
  refine ⟨⋂ i, G i, MeasurableSet.iInter hG, ?_, Finset.univ.sup N₀, ?_⟩
  · rw [compl_iInter]
    calc
      μ (⋃ i, (G i)ᶜ) ≤ ∑ i, μ (G i)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : I, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => hGμ i)
      _ = ENNReal.ofReal ((Fintype.card I : ℝ) * a) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => ha.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [a]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card I + 1)]
        nlinarith
  · intro x hx i N hNlarge
    exact hN i x (mem_iInter.mp hx i) N
      ((Finset.le_sup (Finset.mem_univ i)).trans hNlarge)

/-- The common good set applies to an actual ergodic component of a
root flow on the arithmetic quotient. -/
theorem exists_finite_uniform_root_flow_generic_set
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) {I : Type*} [Fintype I]
    (ν : Measure (X n)) [IsProbabilityMeasure ν]
    (herg : let := rootTranslationAction hij
      ErgodicSMul (Multiplicative ℝ) (X n) ν)
    (f : I → X n →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set (X n), MeasurableSet G ∧ ν Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ a, ∀ N ≥ N₀,
        |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ),
            f a (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) -
          ∫ y, f a y ∂ν| ≤ ε := by
  let := rootTranslationAction hij
  let : ContinuousSMul (Multiplicative ℝ) (X n) := rootTranslationAction_continuous hij
  let : ErgodicSMul (Multiplicative ℝ) (X n) ν := herg
  have hact (t : ℝ) (x : X n) : realActionTime t x =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := rfl
  simpa only [hact] using
    exists_finite_uniform_integer_flow_generic_set ν f ε δ hε hδ

end DukePrimeDegree

end

end OAI
