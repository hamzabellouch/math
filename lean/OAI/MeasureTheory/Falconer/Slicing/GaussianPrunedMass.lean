import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedIncidence

namespace OAI

/-! # Uniform masses and support of the pruned original slice laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianPointSliceMeasure_ae_of_ae
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂gaussianPointSliceMeasure μ A z δ, P x := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

theorem gaussianPointGood_mass
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (i : ι) (hi : D < r i) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)) univ ≤ T i := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)
  have ha : ∀ᵐ x ∂α, x ∈ ball 0 (r i) := by
    filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ p.1 p.2 δ hμ)] with x hx
    simpa only [mem_ball,dist_zero_right] using hx.trans_lt hi
  have he : α (ball 0 (r i)) = α univ := measure_congr (by
    filter_upwards [ha] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
  rw [← he]
  exact gaussianPointGood_ball μ δ r T p i 0

theorem gaussian_pruned_incidence_le_masses
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M E p ≤
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ *
      ((gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)) univ := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  change (α.prod β) E ≤ α univ*β univ
  calc
    _ ≤ (α.prod β) univ := measure_mono (subset_univ _)
    _ = _ := by rw [← univ_prod_univ,Measure.prod_prod]

end Falconer

end OAI
