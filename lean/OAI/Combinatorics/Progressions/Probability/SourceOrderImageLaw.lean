import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem product_image_law_swap {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (U : X × Y → Z) (hU : Measurable U) :
    (ν.prod μ).map (fun p => U (p.2, p.1)) = (μ.prod ν).map U := by
  have hs : Measurable (fun p : Y × X => U (p.2, p.1)) := hU.comp measurable_swap
  rw [← Measure.prod_swap (μ := μ) (ν := ν), Measure.map_map hs measurable_swap]
  rfl

theorem product_image_law_assoc {X Y Z W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure X) (ν : Measure Y) (ξ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ξ]
    (U : X × (Y × Z) → W) (hU : Measurable U) :
    ((μ.prod ν).prod ξ).map (fun p => U (p.1.1, p.1.2, p.2)) = (μ.prod (ν.prod ξ)).map U := by
  rw [← Measure.prodAssoc_prod, Measure.map_map hU MeasurableEquiv.prodAssoc.measurable]
  rfl

end Erdos3

end

end OAI
