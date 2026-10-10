import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedPair

namespace OAI

/-! # Null original fiber losses stay null for every retained slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem product_inter_eq_of_null_original_fibers
    (μ α : Measure X) (β : Measure W) [SFinite α] [SFinite β] (hα : α ≪ μ)
    (E F : Set (X × W)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) :
    (α.prod β) (E ∩ F) = (α.prod β) E := by
  have hz : (α.prod β) (E \ F) = 0 := by
    rw [Measure.prod_apply_symm (hE.diff hF)]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun w => hα (hzero w))
  apply measure_congr
  have hnot : ∀ᵐ t ∂α.prod β, t ∉ E \ F := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hnot] with t ht
  simp only [mem_sdiff] at ht
  apply propext
  simp only [mem_inter_iff]
  tauto

theorem gaussian_pruned_inter_eq_of_null_original_fibers {d h : ℕ} {ι : Type*}
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E F : Set (Space d × Sphere d)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0)
    (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M (E ∩ F) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  apply product_inter_eq_of_null_original_fibers μ _ _ _ E F hE hF hzero
  exact Measure.absolutelyContinuous_restrict.trans
    (Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict)

end Falconer

end OAI
