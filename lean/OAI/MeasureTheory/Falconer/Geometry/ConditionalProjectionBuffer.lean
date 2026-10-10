import OAI.MeasureTheory.Falconer.Geometry.ProjectionBuffer
import OAI.MeasureTheory.Falconer.Estimates.RescaledConditional

namespace OAI

/-! # Projection buffers for the full original conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem conditional_pair_diameter (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) :
    ∀ᵐ z : Space d × Space d ∂
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier).prod
        (ProbabilityTheory.cond ρ (Q.descendant P).carrier),
      ‖z.1-z.2‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^P.length) := by
  have hs : ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      z ∈ (Q.descendant P).carrier :=
    ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable (fun _ hz => hz)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  have hh := (Q.descendant P).dist_le (by rw [Q.descendant_side]; positivity) hx hy
  simpa only [dist_eq_norm,Q.descendant_side] using hh

theorem conditional_projection_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W' T) :
    v ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T := by
  apply projectionGoodSet_buffer _ (by positivity) hδ _ hvw hwidth hw
  simpa only [hQ,mul_one_div] using conditional_pair_diameter Q (by rw [hQ]; norm_num) ρ P

end Falconer.Regularization

end OAI
