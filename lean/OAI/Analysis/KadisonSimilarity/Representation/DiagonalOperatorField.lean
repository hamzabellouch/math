import OAI.Analysis.KadisonSimilarity.Representation.AEColumnOperator
import OAI.Analysis.KadisonSimilarity.Representation.L2Localization

namespace OAI

/-! # The field of a diagonal-commuting L² operator

An operator commuting with every measurable localization has bounded
constant-vector columns. Those actual columns determine a field of bounded
operators on a measurable conull subset of the base, without any additional
pointwise linearity assumption.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Reconstruct the pointwise operator from its actual constant-vector
columns. Each fixed column is preserved almost everywhere. -/
theorem exists_conull_diagonal_operator_field
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ field : ∀ _a : s, H →L[ℂ] H,
        (∀ a, ‖field a‖ ≤ ‖T‖) ∧
        ∀ x : H, ∀ᵐ a ∂Measure.comap ((↑) : s → Ω) μ,
          field a x = T (Lp.const 2 μ x) a := by
  let U : H →L[ℂ] Lp H 2 μ := T.comp (Lp.constL 2 μ ℂ)
  apply exists_conull_columnOperators μ (fun _ => H) ‖T‖₊ (fun x a => U x a)
  · filter_upwards [Lp.coeFn_zero H 2 μ] with a ha
    simpa only [map_zero, Pi.zero_apply] using ha
  · intro x y
    filter_upwards [Lp.coeFn_add (U x) (U y)] with a ha
    simpa only [map_add, Pi.add_apply] using ha
  · intro x
    filter_upwards [Lp.coeFn_smul Complex.I (U x)] with a ha
    simpa only [map_smul, Pi.smul_apply] using ha
  · intro x
    exact diagonal_commutant_column_bound μ T hT x

end KadisonSimilarity

end

end OAI
