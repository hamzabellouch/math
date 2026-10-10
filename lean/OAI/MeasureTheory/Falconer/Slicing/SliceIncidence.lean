import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # The real incidence integral of the normalized original slice laws -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem slice_iterated_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (X × Y)) (hE : MeasurableSet E) :
    (∫ y, ∫ x, if (x,y) ∈ E then (1 : ℝ) else 0 ∂μ ∂ν) = (μ.prod ν).real E := by
  have hi : Integrable (E.indicator (fun _ : X × Y => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hE
  have he := integral_prod_symm (E.indicator (fun _ : X × Y => (1 : ℝ))) hi
  rw [integral_indicator_const (1 : ℝ) hE,smul_eq_mul,mul_one] at he
  exact he.symm

theorem normalized_slice_iterated_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0)
    (E : Set (X × Y)) (hE : MeasurableSet E) :
    (∫ y, ∫ x, if (x,y) ∈ E then (1 : ℝ) else 0
      ∂(normalizedSliceLaw μ hμ : Measure X) ∂(normalizedSliceLaw ν hν : Measure Y)) =
      ((μ univ*ν univ)⁻¹*(μ.prod ν) E).toReal := by
  rw [slice_iterated_incidence _ _ E hE,Measure.real,normalizedSliceLaw_incidence]

end Falconer

end OAI
