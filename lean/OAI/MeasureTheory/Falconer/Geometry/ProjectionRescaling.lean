import OAI.MeasureTheory.Falconer.Geometry.ProjectionLaw

namespace OAI

/-! # Projection collisions under the actual cell rescaling -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_cellScaleMap (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (p : ℕ) (c w : Space d) (W : ℝ) :
    projectionCollision (Measure.map (Regularization.cellScaleMap p c) ρ) w ((2:ℝ)^p*W) =
      projectionCollision ρ w W := by
  have hm := (Regularization.cellScaleMap_continuous p c).measurable
  rw [projectionCollision,Measure.map_prod_map ρ ρ hm hm,
    Measure.map_apply (hm.prodMap hm) (by measurability)]
  congr 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,Prod.map_fst,Prod.map_snd]
  have he : Regularization.cellScaleMap p c z.1-Regularization.cellScaleMap p c z.2 =
      (2:ℝ)^p • (z.1-z.2) := by unfold Regularization.cellScaleMap; module
  have hp : 0 < (2:ℝ)^p := by positivity
  rw [he,real_inner_smul_left,abs_mul,abs_of_pos hp]
  exact mul_le_mul_iff_right₀ hp

end Falconer

end OAI
