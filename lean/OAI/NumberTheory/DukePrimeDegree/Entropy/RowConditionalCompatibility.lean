import OAI.NumberTheory.DukePrimeDegree.Geometry.RowReducedChart
import OAI.NumberTheory.DukePrimeDegree.Entropy.NestedRealConditionals

namespace OAI

/-!
# Nested row conditionals agree with one-root conditionals

The explicit row/root coordinate change transports the real conditional
in a row disintegration to the conditional in the existing one-root
chart. This is the chart compatibility needed to apply the root-leaf
holonomy theorem inside the row-product argument.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace DukePrimeDegree
open PrimeDegreePackets

def rowSplitMeasure {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) :
    Measure (RowRootSlice i k × (RowRemainingTime i j × ℝ)) :=
  ρ.map (Prod.map id (rowTimeSplit hij))

instance rowSplitMeasure_finite {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (rowSplitMeasure hij ρ) := by unfold rowSplitMeasure; infer_instance

def rowSingleMeasure {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) : Measure (RootSlice i j k × ℝ) :=
  ((rowSplitMeasure hij ρ).map MeasurableEquiv.prodAssoc.symm).map
    (Prod.map (rowReducedHomeomorph hij k).symm id)

instance rowSingleMeasure_finite {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (rowSingleMeasure hij ρ) := by unfold rowSingleMeasure; infer_instance

theorem row_conditional_compatibility {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) [IsFiniteMeasure ρ] :
    ∀ᵐ s ∂(rowSplitMeasure hij ρ).fst,
      ∀ᵐ w ∂((rowSplitMeasure hij ρ).condKernel s).fst,
        (rowSingleMeasure hij ρ).condKernel ((rowReducedHomeomorph hij k).symm (s, w)) =
          ((rowSplitMeasure hij ρ).condKernel s).condKernel w := by
  let σ := rowSplitMeasure hij ρ
  let η := σ.map MeasurableEquiv.prodAssoc.symm
  let κ := σ.condKernel
  have hη : η = (σ.fst ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    calc
      η = (σ.fst ⊗ₘ (κ.fst ⊗ₖ κ.condKernel)).map MeasurableEquiv.prodAssoc.symm := by
        rw [Kernel.disintegrate, Measure.disintegrate]
      _ = _ := Measure.compProd_assoc
  have hf : η.fst = σ.fst ⊗ₘ κ.fst := by rw [hη, Measure.fst_compProd]
  have hm := condKernel_map_measurableEquiv η
    (rowReducedHomeomorph hij k).symm.toMeasurableEquiv (MeasurableEquiv.refl ℝ)
  have hh : ∀ᵐ z ∂η.fst,
      (rowSingleMeasure hij ρ).condKernel ((rowReducedHomeomorph hij k).symm z) =
        η.condKernel z := by
    filter_upwards [hm] with z hz
    change (rowSingleMeasure hij ρ).condKernel ((rowReducedHomeomorph hij k).symm z) =
      (η.condKernel z).map id at hz
    simpa only [Measure.map_id] using hz
  rw [hf] at hh
  have hp := Measure.ae_ae_of_ae_compProd hh
  filter_upwards [hp, ae_nested_real_conditionals σ] with s hs hc
  filter_upwards [hs, hc] with w hw hcw
  exact hw.trans hcw

end DukePrimeDegree

end

end OAI
