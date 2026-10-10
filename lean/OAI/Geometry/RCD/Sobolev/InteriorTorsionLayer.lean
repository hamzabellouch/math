import OAI.Geometry.RCD.Sobolev.InteriorTorsionBounds

namespace OAI

/-! # Relating the quadratic torsion scale to a metric boundary layer -/

open Set Metric Laplacian
noncomputable section
namespace RegularPointCoordinates

theorem interior_torsion_layer {n : ℕ} {R δ : ℝ}
    (hR : 0<R) (hδ : 0<δ) (hsmall : 4*δ≤R) :
    ∃ b : ℝ, R-δ<b ∧ b<R ∧
      tsupport (euclideanInteriorTorsion n R (R*δ/4))⊆ball 0 b ∧
      ∀ x∈ball (0:Euclidean n) (R-δ),
        (Δ (euclideanInteriorTorsion n R (R*δ/4))) x= -2*(n:ℝ) := by
  have ht : 0<R*δ/4 := by positivity
  have htR : R*δ/4<R^2 := by nlinarith
  have hroot := Real.sq_sqrt (show 0≤R^2-R*δ/4 by linarith)
  have hroot0 := Real.sqrt_nonneg (R^2-R*δ/4)
  have hrootR : Real.sqrt (R^2-R*δ/4)<R := by nlinarith
  have haroot : R-δ<Real.sqrt (R^2-R*δ/4) := by nlinarith
  let b := (Real.sqrt (R^2-R*δ/4)+R)/2
  have hqb : Real.sqrt (R^2-R*δ/4)<b := by dsimp only [b]; linarith
  refine ⟨b,haroot.trans hqb,by dsimp only [b]; linarith,
    (euclideanInteriorTorsion_support n R ht htR).trans (closedBall_subset_ball hqb),?_⟩
  intro x hx
  apply euclideanInteriorTorsion_laplacian_core R ht
  have hnorm : ‖x‖<R-δ := by simpa only [mem_ball,dist_zero_right] using hx
  have hs : ‖x‖^2<(R-δ)^2 :=
    (sq_lt_sq₀ (norm_nonneg x) (by linarith : 0≤R-δ)).mpr hnorm
  dsimp only [euclideanQuadraticDefect]
  nlinarith

end RegularPointCoordinates

end

end OAI
