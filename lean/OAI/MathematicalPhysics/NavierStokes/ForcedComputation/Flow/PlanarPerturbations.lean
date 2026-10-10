import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionPerturbations

namespace OAI

/-! Quantitative stability of the planar Hamiltonian slices, using the
integer derivative bound computed from their finite expression. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped NNReal

theorem horizontal_norm_le (v : Space) : ‖horizontal v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro j
  fin_cases j
  · exact norm_le_pi_norm v 0
  · exact norm_le_pi_norm v 1

theorem atHeight_zero_norm (x : Plane) : ‖atHeight x 0‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro j
    fin_cases j
    · exact norm_le_pi_norm x 0
    · exact norm_le_pi_norm x 1
    · change ‖(0 : ℝ)‖ ≤ ‖x‖
      simpa only [norm_zero] using norm_nonneg x
  · simpa only [atHeight_horizontal] using horizontal_norm_le (atHeight x 0)

theorem atHeight_dist_same (x y : Plane) (z : ℝ) :
    dist (atHeight x z) (atHeight y z) = dist x y := by
  have he : atHeight x z - atHeight y z = atHeight (x - y) 0 := by
    funext j
    fin_cases j <;> simp [atHeight]
  rw [dist_eq_norm, he, atHeight_zero_norm, dist_eq_norm]

def planarSlice (H : FieldExpr) (s : ℝ) (x : Plane) : Plane :=
  PlanarHamiltonian.field (fun Y => SpatialExpression.spatialValue H (atHeight Y s)) x

theorem planarSlice_eq_horizontal {H : FieldExpr} (hH : H.Valid) (s : ℝ) (x : Plane) :
    planarSlice H s x = horizontal (SpatialExpression.suspensionField H (atHeight x s)) := by
  rw [suspensionField_atHeight hH, atHeight_horizontal]
  rfl

theorem planarSlice_lipschitz {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) :
    LipschitzWith (suspensionLipschitzBound H : ℝ≥0) (planarSlice H s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [planarSlice_eq_horizontal hH, planarSlice_eq_horizontal hH]
  have hp : dist (horizontal (SpatialExpression.suspensionField H (atHeight x s)))
      (horizontal (SpatialExpression.suspensionField H (atHeight y s))) ≤
      dist (SpatialExpression.suspensionField H (atHeight x s))
        (SpatialExpression.suspensionField H (atHeight y s)) := by
    have he : horizontal (SpatialExpression.suspensionField H (atHeight x s) -
        SpatialExpression.suspensionField H (atHeight y s)) =
        horizontal (SpatialExpression.suspensionField H (atHeight x s)) -
          horizontal (SpatialExpression.suspensionField H (atHeight y s)) := by
      funext j
      fin_cases j <;> rfl
    simpa only [he, dist_eq_norm] using horizontal_norm_le
      (SpatialExpression.suspensionField H (atHeight x s) -
        SpatialExpression.suspensionField H (atHeight y s))
  exact hp.trans (by simpa only [atHeight_dist_same] using
    (suspensionField_lipschitz hH hT).dist_le_mul (atHeight x s) (atHeight y s))

theorem planarSlice_fderiv_bound {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) (s : ℝ) (x : Plane) :
    ‖fderiv ℝ (planarSlice H s) x‖ ≤ (suspensionLipschitzBound H : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ (planarSlice_lipschitz hH hT s)

theorem planar_trajectory_perturbation {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {ψ χ : ℝ → Plane} {a b : ℝ}
    (hψ : ∀ s ∈ Icc a b, HasDerivAt ψ (planarSlice H s (ψ s)) s)
    (hχ : ∀ s ∈ Icc a b, HasDerivAt χ (planarSlice H s (χ s)) s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    dist (ψ t) (χ t) ≤ dist (ψ a) (χ a) *
      Real.exp ((suspensionLipschitzBound H : ℝ) * (t - a)) := by
  have hcψ : ContinuousOn ψ (Icc a b) :=
    fun s hs => (hψ s hs).continuousAt.continuousWithinAt
  have hcχ : ContinuousOn χ (Icc a b) :=
    fun s hs => (hχ s hs).continuousAt.continuousWithinAt
  exact dist_le_of_trajectories_ODE (planarSlice_lipschitz hH hT) hcψ
    (fun s hs => (hψ s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) hcχ
    (fun s hs => (hχ s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) le_rfl t ht

end ForcedComputation

end

end OAI
