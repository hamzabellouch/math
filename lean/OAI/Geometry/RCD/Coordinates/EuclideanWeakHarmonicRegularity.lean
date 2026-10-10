import OAI.Geometry.RCD.Sobolev.EuclideanWeakHarmonicMean

namespace OAI

/-! # Classical harmonicity from the local compact-test Laplace equation -/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped ContDiff Convolution Topology
noncomputable section
namespace RegularPointCoordinates

theorem compact_continuous_weak_harmonic {n : ℕ} {f : Euclidean n → ℝ} {S : ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (hw : EuclideanWeakHarmonicOn f S) :
    HarmonicOnNhd f (ball 0 S) := by
  intro p hp
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
  apply (harmonicAt_congr_nhds he).mpr
  exact ((weak_harmonic_convolution hf.locallyIntegrable (euclideanRadialKernel_smooth n r)
    (euclideanRadialKernel_compact n hr) (euclideanRadialKernel_support n hr) hw) p hpr).const_smul

theorem EuclideanWeakHarmonicOn.congr {n : ℕ} {f g : Euclidean n → ℝ} {S : ℝ}
    (hf : EuclideanWeakHarmonicOn f S) (he : EqOn f g (ball 0 S)) :
    EuclideanWeakHarmonicOn g S := by
  intro ψ hψ
  calc
    (∫ y, g y*(Laplacian.laplacian ψ) y) = ∫ y, f y*(Laplacian.laplacian ψ) y := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y∈tsupport ψ
      · rw [he (hψ.2.2 hy)]
      · rw [laplacian_eq_zero_of_notMem_tsupport ψ hy,mul_zero,mul_zero]
    _ = 0 := hf ψ hψ

theorem EuclideanWeakHarmonicOn.mono {n : ℕ} {f : Euclidean n → ℝ} {S R : ℝ}
    (hf : EuclideanWeakHarmonicOn f S) (hRS : R≤S) : EuclideanWeakHarmonicOn f R := by
  intro ψ hψ
  exact hf ψ ⟨hψ.1,hψ.2.1,hψ.2.2.trans (ball_subset_ball hRS)⟩

theorem continuous_mul_of_tsupport_subset {E : Type*} [TopologicalSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f χ : E → ℝ}
    (hf : ContinuousOn f Ω) (hχ : Continuous χ) (hs : tsupport χ ⊆ Ω) :
    Continuous (fun x => χ x*f x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈Ω
  · exact hχ.continuousAt.mul (hf.continuousAt (hΩ.mem_nhds hx))
  · have ht : x∉tsupport χ := fun h => hx (hs h)
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    simp only [hy,Pi.zero_apply,zero_mul]

theorem continuous_weak_harmonic {n : ℕ} {f : Euclidean n → ℝ} {S : ℝ}
    (hf : ContinuousOn f (ball 0 S)) (hw : EuclideanWeakHarmonicOn f S) :
    HarmonicOnNhd f (ball 0 S) := by
  intro p hp
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
  apply (harmonicAt_congr_nhds hevent).mp
  exact compact_continuous_weak_harmonic hFc hFs hFw p hpa

end RegularPointCoordinates

end

end OAI
