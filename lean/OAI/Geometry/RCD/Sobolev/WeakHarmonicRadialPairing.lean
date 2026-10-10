import OAI.Geometry.RCD.Sobolev.WeakHarmonicWeightedPairing
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! # Identifying the radial pairing by the Euclidean weak equation -/

open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates

theorem gradient_half_norm_sq {n : ℕ} (x : Euclidean n) :
    gradient (fun y : Euclidean n => ‖y‖^2/2) x=x := by
  have he : (fun y : Euclidean n => ‖y‖^2/2)=(fun y => (1/2:ℝ)*‖y‖^2) := by
    funext y
    ring
  have hd : fderiv ℝ (fun y : Euclidean n => ‖y‖^2/2) x=innerSL ℝ x := by
    have hn : DifferentiableAt ℝ (fun y : Euclidean n => ‖y‖^2) x :=
      (hasStrictFDerivAt_norm_sq x).differentiableAt
    rw [he,fderiv_const_mul hn]
    rw [fderiv_norm_sq_apply]
    ext y
    norm_num [smul_eq_mul]
    ring
  simp only [gradient,hd]
  exact (toDual ℝ (Euclidean n)).symm_apply_apply x

theorem weak_harmonic_radial_pairing {n : ℕ} {S : ℝ} (hS : 0<S)
    {g ψ : Euclidean n → ℝ}
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hweak : EuclideanWeakHarmonicOn g S) (hψ : InteriorSmoothTest n S ψ)
    (h₁ : Integrable (fun x => (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient g x)) volume)
    (h₂ : Integrable (fun x => ψ x*fderiv ℝ g x x) volume) :
    (∫ x, (‖x‖^2/2)*inner ℝ (gradient ψ x) (gradient g x))=
      -(∫ x, ψ x*fderiv ℝ g x x) := by
  have hq : ContDiff ℝ ∞ (fun y : Euclidean n => ‖y‖^2/2) :=
    (contDiff_id.norm_sq ℝ).div_const 2
  have hp (x : Euclidean n) :
      inner ℝ (gradient (fun y : Euclidean n => ‖y‖^2/2) x) (gradient g x)=fderiv ℝ g x x := by
    rw [gradient_half_norm_sq,real_inner_comm,inner_gradient_left]
  simpa only [hp] using weak_harmonic_weighted_pairing hS hg hweak hq hψ h₁
    (by simpa only [hp] using h₂)

end RegularPointCoordinates

end

end OAI
