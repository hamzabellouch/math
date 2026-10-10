import OAI.MeasureTheory.Falconer.Slicing.SliceMapBalls
import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelCoordinates
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass

namespace OAI

/-! # Finite-scale ball bounds on the actual kernel-coordinate pushforwards -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_kernel_ball_bound (A : Fin h → Space d) (z : Space h)
    (μ : Measure (Space d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hμ : ∀ᵐ x ∂μ, x ∈ gaussianPointBand A z δ)
    (hball : ∀ x, μ (ball x R) ≤ C) (hR : 2*s+K*((h:ℝ)*(2*δ)) ≤ R) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection μ) (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control μ _
    (gaussianRowMap A).ker.starProjection.continuous.measurable _ hμ _ hball a
  intro x hx y hy hxy
  have hp := gaussian_point_kernel_pair_distance A z hK hbound hx hy
    (le_refl ‖(gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection y‖)
  rw [dist_eq_norm] at hxy ⊢
  exact hp.trans_lt (by linarith)

theorem gaussian_direction_kernel_ball_bound (A : Fin h → Space d)
    (ν : Measure (Sphere d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hν : ∀ᵐ w ∂ν, w ∈ gaussianDirectionBand A δ)
    (hball : ∀ w, ν (ball w R) ≤ C) (hR : 2*s+4*(K*((h:ℝ)*δ)) ≤ R) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d))) ν)
      (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control ν _ (by unfold NormedSpace.normalize; fun_prop) _ hν _ hball a
  intro w hw v hv hdist
  have hwe := gaussian_direction_kernel_normalize_error A hK hbound hsmall hw
  have hve := gaussian_direction_kernel_normalize_error A hK hbound hsmall hv
  change ‖(w:Space d)-(v:Space d)‖ < R
  rw [dist_eq_norm] at hdist
  have htriangle : ‖(w:Space d)-(v:Space d)‖ ≤
      ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-
        normalize ((gaussianRowMap A).ker.starProjection (v:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (v:Space d))-(v:Space d)‖ := by
    calc
      _ ≤ ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
          ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(v:Space d)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub
          (normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
          (normalize ((gaussianRowMap A).ker.starProjection (v:Space d))) (v:Space d)
        exact (add_le_add le_rfl ht).trans_eq (add_assoc _ _ _).symm
  have hwe' : ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ ≤
      2*(K*((h:ℝ)*δ)) := (norm_sub_rev _ _).le.trans hwe
  linarith

end Falconer

end OAI
