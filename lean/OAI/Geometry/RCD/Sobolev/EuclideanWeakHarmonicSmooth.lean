import OAI.Geometry.RCD.Coordinates.EuclideanWeakHarmonicRegularity

namespace OAI

/-! # Smoothness needed to recover the actual local harmonic model

The proved radial mean identity identifies the function locally with a
convolution against a compact smooth kernel, at every derivative order.
-/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped ContDiff Convolution Topology
noncomputable section
namespace RegularPointCoordinates

theorem compact_continuous_weak_harmonic_smooth {n : ℕ} {f : Euclidean n → ℝ} {S : ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (hw : EuclideanWeakHarmonicOn f S) :
    ContDiffOn ℝ ∞ f (ball 0 S) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hpS : ‖p‖<S := by simpa only [mem_ball,dist_zero_right] using hp
  let r := (S-‖p‖)/2
  have hr : 0<r := by dsimp only [r]; linarith
  have hpr : p∈ball (0:Euclidean n) (S-r) := by
    simp only [mem_ball,dist_zero_right]
    dsimp only [r]
    linarith
  let C := r^n*(∫ x, euclideanRadialWeight n x)
  have hC : C≠0 := (mul_pos (pow_pos hr _) (euclideanRadialWeight_mass_pos n)).ne'
  have he : f =ᶠ[𝓝 p] C⁻¹ •
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r) := by
    filter_upwards [isOpen_ball.mem_nhds hpr] with y hy
    have hyS : ‖y‖+r<S := by
      have hyt : ‖y‖<S-r := by simpa only [mem_ball,dist_zero_right] using hy
      linarith
    have hm := weak_harmonic_radial_mean hf hfs hw hr y hyS
    change f y=C⁻¹*((f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r) y)
    rw [hm]
    exact (inv_mul_cancel_left₀ hC (f y)).symm
  exact (((euclideanRadialKernel_compact n hr).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable (euclideanRadialKernel_smooth n r)).const_smul
      (C⁻¹)).contDiffAt.congr_of_eventuallyEq he

theorem continuous_weak_harmonic_smooth {n : ℕ} {f : Euclidean n → ℝ} {S : ℝ}
    (hf : ContinuousOn f (ball 0 S)) (hw : EuclideanWeakHarmonicOn f S) :
    ContDiffOn ℝ ∞ f (ball 0 S) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hpS : ‖p‖<S := by simpa only [mem_ball,dist_zero_right] using hp
  let a := (S+‖p‖)/2
  let b := (S+a)/2
  have ha : 0<a := by dsimp only [a]; linarith [norm_nonneg p]
  have hab : a<b := by dsimp only [a,b]; linarith
  have hbS : b<S := by dsimp only [a,b]; linarith
  let χ : ContDiffBump (0:Euclidean n) := ⟨a,b,ha,hab⟩
  let F := fun x => χ x*f x
  have hFc : Continuous F := continuous_mul_of_tsupport_subset isOpen_ball hf χ.continuous
    (by rw [χ.tsupport_eq]; exact closedBall_subset_ball hbS)
  have hFs : HasCompactSupport F := χ.hasCompactSupport.mul_right
  have he : EqOn F f (ball 0 a) := by
    intro x hx
    change χ x*f x=f x
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx),one_mul]
  have hFw : EuclideanWeakHarmonicOn F a :=
    (hw.mono (by dsimp only [a]; linarith)).congr he.symm
  have hpa : p∈ball (0:Euclidean n) a := by
    simp only [mem_ball,dist_zero_right]
    dsimp only [a]
    linarith
  have hevent : F =ᶠ[𝓝 p] f := by
    filter_upwards [isOpen_ball.mem_nhds hpa] with y hy
    exact he hy
  exact ((compact_continuous_weak_harmonic_smooth hFc hFs hFw).contDiffAt
    (isOpen_ball.mem_nhds hpa)).congr_of_eventuallyEq hevent.symm

end RegularPointCoordinates

end

end OAI
