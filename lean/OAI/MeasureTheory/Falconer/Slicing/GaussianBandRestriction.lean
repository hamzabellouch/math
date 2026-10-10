import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedPair

namespace OAI

/-! # Making the two slice bands explicit in the original-label relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_inter_bands
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (gaussianPointBand p.1 p.2 δ ×ˢ gaussianDirectionBand p.1 δ)) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  have hp : ∀ᵐ x ∂α, x ∈ gaussianPointBand p.1 p.2 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)
  have hw : ∀ᵐ w ∂β, w ∈ gaussianDirectionBand p.1 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)
  change (α.prod β) _ = (α.prod β) E
  apply measure_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,Measure.quasiMeasurePreserving_snd.ae hw] with t ht hu
  exact propext ⟨fun h => h.1,fun h => ⟨h,ht,hu⟩⟩

end Falconer

end OAI
