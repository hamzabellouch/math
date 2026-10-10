import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowNonautonomous
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition

namespace OAI

/-! The time-augmented smooth-flow theorem applied to the actual finite
Hamiltonian expression used by the planar processor. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff NNReal

def phaseSpacePoint (p : ℝ × Plane) : Space := atHeight p.2 p.1

theorem phaseSpacePoint_smooth : ContDiff ℝ ∞ phaseSpacePoint := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun p : ℝ × Plane => p.2 0)
    exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  · change ContDiff ℝ ∞ (fun p : ℝ × Plane => p.2 1)
    exact (contDiff_apply ℝ ℝ 1).comp contDiff_snd
  · exact contDiff_fst

theorem phaseSpacePoint_lipschitz : LipschitzWith 1 phaseSpacePoint := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (p - q))).mpr
  intro j
  fin_cases j
  · exact (norm_le_pi_norm (p.2 - q.2) 0).trans (norm_snd_le (p - q))
  · exact (norm_le_pi_norm (p.2 - q.2) 1).trans (norm_snd_le (p - q))
  · exact norm_fst_le (p - q)

theorem horizontal_smooth : ContDiff ℝ ∞ horizontal := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> exact contDiff_apply ℝ ℝ _

theorem horizontal_lipschitz : LipschitzWith 1 horizontal := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : horizontal (x - y) = horizontal x - horizontal y := by
    ext j
    fin_cases j <;> rfl
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, he] using horizontal_norm_le (x - y)

theorem planarSlice_joint_smooth {H : FieldExpr} (hH : H.Valid) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => planarSlice H p.1 p.2) := by
  have he : (fun p : ℝ × Plane => planarSlice H p.1 p.2) =
      horizontal ∘ SpatialExpression.suspensionField H ∘ phaseSpacePoint := by
    funext p
    exact planarSlice_eq_horizontal hH p.1 p.2
  rw [he]
  exact horizontal_smooth.comp
    ((SpatialExpression.suspensionField_smooth hH).comp phaseSpacePoint_smooth)

theorem planarSlice_joint_lipschitz {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) :
    LipschitzWith (suspensionLipschitzBound H : ℝ≥0)
      (fun p : ℝ × Plane => planarSlice H p.1 p.2) := by
  have h := horizontal_lipschitz.comp
    ((suspensionField_lipschitz hH hT).comp phaseSpacePoint_lipschitz)
  simpa only [one_mul, mul_one, Function.comp_def, phaseSpacePoint,
    ← planarSlice_eq_horizontal hH] using h

theorem planarTransition_joint_smooth {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ω : ℝ → ℝ → Plane → Plane}
    (hΩ : IsPlanarTransition (planarSlice H) Ω) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Plane) => Ω p.1 p.2.1 p.2.2) :=
  Flow.transition_contDiff
    ⟨_, (planarSlice_joint_smooth hH).continuous⟩
    (planarSlice_joint_smooth hH) (planarSlice_joint_lipschitz hH hT)
    hΩ.ode hΩ.initial

theorem planarTransition_backward_smooth {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ω : ℝ → ℝ → Plane → Plane}
    (hΩ : IsPlanarTransition (planarSlice H) Ω) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => Ω p.1 (-p.1) p.2) :=
  (planarTransition_joint_smooth hH hT hΩ).comp
    (contDiff_fst.prodMk (contDiff_fst.neg.prodMk contDiff_snd))

end ForcedComputation

end

end OAI
