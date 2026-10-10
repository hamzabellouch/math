import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

namespace OAI

open scoped ENNReal
open MeasureTheory MeasureTheory.Measure

namespace InvariantProjection.TriangularProbability

theorem ae_ne_prod (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
  apply (ae_prod_iff_ae_ae measurableSet_diagonal.compl).2
  exact Filter.Eventually.of_forall fun x => (μ.ae_ne x).mono fun y hy => Ne.symm hy

theorem measure_strict_triangle (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : (μ.prod μ) {z : ℝ × ℝ | z.1 < z.2} = 1 / 2 := by
  let E : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let F : Set (ℝ × ℝ) := {z | z.2 < z.1}
  have hE : MeasurableSet E := measurableSet_lt measurable_fst measurable_snd
  have hF : MeasurableSet F := measurableSet_lt measurable_snd measurable_fst
  have hswap : (μ.prod μ) E = (μ.prod μ) F := by
    calc
      (μ.prod μ) E = ((μ.prod μ).map Prod.swap) E := by rw [prod_swap]
      _ = (μ.prod μ) F := by rw [Measure.map_apply measurable_swap hE]; rfl
  have hcompl : Eᶜ =ᵐ[μ.prod μ] F := by
    filter_upwards [ae_ne_prod μ] with z hz
    change (¬ z.1 < z.2) = (z.2 < z.1)
    apply propext
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hz),
      fun h => not_lt_of_gt h⟩
  have hsum : (μ.prod μ) E + (μ.prod μ) E = 1 := by
    calc
      (μ.prod μ) E + (μ.prod μ) E = (μ.prod μ) E + (μ.prod μ) F :=
        congrArg (fun r => (μ.prod μ) E + r) hswap
      _ = (μ.prod μ) E + (μ.prod μ) Eᶜ :=
        congrArg (fun r => (μ.prod μ) E + r) (measure_congr hcompl).symm
      _ = 1 := by rw [measure_add_measure_compl hE, measure_univ]
  have hfinite : (μ.prod μ) E ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' hfinite (by norm_num)).mp
  have hsreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfinite hfinite] at hsreal
  norm_num at hsreal ⊢
  linarith

end InvariantProjection.TriangularProbability

end OAI
