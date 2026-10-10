import OAI.MeasureTheory.Falconer.Slicing.GnomonicSliceLaw
import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningSets

namespace OAI

/-! # Exact transport of restricted original chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

lemma gaussianDirectionGood_measurable_fixed {d : ℕ} {ι : Type*} [Fintype ι]
    (ν : Measure (Sphere d)) [SFinite ν] (δ : ℝ) (r : ι → ℝ)
    (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    MeasurableSet (gaussianDirectionGood ν δ r T M A) := by
  let f : Sphere d → (Fin h → Space d) × Sphere d := fun w => (A,w)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  have hj : MeasurableSet {p : (Fin h → Space d) × Sphere d |
      p.2 ∈ gaussianDirectionGood ν δ r T M p.1} :=
    gaussianDirectionGood_measurable_joint (h := h) ν δ r T M
  change MeasurableSet (f ⁻¹' {p : (Fin h → Space d) × Sphere d |
    p.2 ∈ gaussianDirectionGood ν δ r T M p.1})
  exact hj.preimage hf

instance gaussianChartSliceMeasure_finite (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    (A : Fin h → Space (n+1)) (δ : ℝ) :
    IsFiniteMeasure (gaussianChartSliceMeasure ν₀ A δ) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (δ^(-(h:ℝ)))*(ν₀.restrict (gnomonicChart ⁻¹' gaussianDirectionBand A δ)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem gnomonic_restricted_slice_map (ν₀ : Measure (Space n))
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Sphere (n+1)))
    (hD : MeasurableSet D) :
    Measure.map gnomonicChart
      ((gaussianChartSliceMeasure ν₀ A δ).restrict (gnomonicChart ⁻¹' D)) =
      (gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict D := by
  rw [← Measure.restrict_map (gnomonicChart_continuous n).measurable hD,
    gaussianChartSlice_map]

theorem gnomonic_restricted_slice_mass (ν₀ : Measure (Space n))
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Sphere (n+1)))
    (hD : MeasurableSet D) :
    ((gaussianChartSliceMeasure ν₀ A δ).restrict (gnomonicChart ⁻¹' D)) univ =
      ((gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict D) univ := by
  rw [← gnomonic_restricted_slice_map ν₀ A δ D hD,
    Measure.map_apply (gnomonicChart_continuous n).measurable MeasurableSet.univ,
    preimage_univ]

theorem gnomonic_incidence_transport {X : Type*} [MeasurableSpace X]
    (α : Measure X) (β : Measure (Space n)) [SFinite α] [SFinite β]
    (E : Set (X × Sphere (n+1))) (hE : MeasurableSet E) :
    (α.prod β) {p | (p.1,gnomonicChart p.2) ∈ E} =
      (α.prod (Measure.map gnomonicChart β)) E := by
  have hm : Measurable (Prod.map (id : X → X) (gnomonicChart : Space n → Sphere (n+1))) :=
    measurable_id.prodMap (gnomonicChart_continuous n).measurable
  have hmap : Measure.map (Prod.map (id : X → X) gnomonicChart) (α.prod β) =
      α.prod (Measure.map gnomonicChart β) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map α β measurable_id (gnomonicChart_continuous n).measurable).symm
  rw [← hmap,Measure.map_apply hm hE]
  rfl

theorem gnomonic_pruned_mass (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    {ι : Type*} [Fintype ι] (A : Fin h → Space (n+1)) (δ : ℝ)
    (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    ((gaussianChartSliceMeasure ν₀ A δ).restrict
      (gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r T M A))
      univ ≤ M := by
  have hD : MeasurableSet (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r T M A) :=
    gaussianDirectionGood_measurable_fixed (Measure.map (gnomonicChart : Space n → Sphere (n+1)) ν₀) δ r T M A
  rw [gnomonic_restricted_slice_mass ν₀ A δ _ hD]
  exact gaussianDirectionGood_mass (Measure.map gnomonicChart ν₀) δ r T M A

end Falconer

end OAI
