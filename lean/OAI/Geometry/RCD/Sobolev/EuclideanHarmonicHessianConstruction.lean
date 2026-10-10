import OAI.Geometry.RCD.Heat.EuclideanRadialKernelDerivative
import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicL1
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # The Euclidean harmonic Hessian input from radial averaging -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Convolution Topology

noncomputable section
namespace RegularPointCoordinates

/-- The exact interior Hessian estimate for normalized harmonic models.
The radius and the function are chosen after the dimensional constant. -/
theorem euclideanHarmonicHessianInput {n : ℕ} (hn : 0 < n) : EuclideanHarmonicHessianInput n := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨C,hC,hconv⟩ := euclideanRadialConvolution_hessian_bound n
  let I := ∫ x, euclideanRadialWeight n x
  have hI : 0 < I := euclideanRadialWeight_mass_pos n
  let V := euclideanUnitVolume n
  have hV : 0 < V := euclideanUnitVolume_pos n
  let M := 64*8^n*C*V/I
  refine ⟨M,by dsimp only [M]; positivity,?_⟩
  intro S hS w z hz
  obtain ⟨F,hF,hFs,hFsupp,hFeq,hFbound,hFharm⟩ := w.wide_compact_extension hS
  have hFint : Integrable F volume := hF.continuous.integrable_of_hasCompactSupport hFs
  have hFL1 := w.extension_l1_le hS hF.continuous hFs
    (hFsupp.trans (closedBall_subset_ball (by linarith : 7*S/8 < S))) hFbound
  let r := S/8
  have hr : 0 < r := by positivity
  let c := r^n*I
  have hc : 0 < c := mul_pos (pow_pos hr _) hI
  let G := F ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r
  have hG : ContDiff ℝ ∞ G := (euclideanRadialKernel_compact n hr).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hFint.locallyIntegrable (euclideanRadialKernel_smooth n r)
  have hmean (y : Euclidean n) (hy : y ∈ ball 0 (S/2)) : G y = c*F y := by
    have hsub : ball y (S/4) ⊆ ball 0 (3*S/4) := by
      apply ball_subset_ball'
      have hd : dist y 0 < S/2 := hy
      linarith
    exact harmonic_convolution_radialKernel hF hFs y (by positivity : 0 < S/4) hr
      (by dsimp only [r]; linarith) (hFharm.mono hsub)
  have heq : w.value =ᶠ[𝓝 z] fun y => c⁻¹ • G y := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    have hsmall : y ∈ ball 0 (3*S/4) := (ball_subset_ball (by linarith : S/2 ≤ 3*S/4)) hy
    rw [smul_eq_mul,hmean y hy,← hFeq y hsmall]
    field_simp
  have hjet := (heq.iteratedFDeriv ℝ 2).self_of_nhds
  have hbound : ‖iteratedFDeriv ℝ 2 G z‖ ≤ (C/r^2)*(∫ y, |F y|) := by
    rw [← norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one]
    exact hconv r hr F hFint z
  have hvolume : volume.real (ball (0 : Euclidean n) S) = S^n*V := by
    rw [Measure.real,Measure.addHaar_ball volume 0 hS.le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),finrank_euclideanSpace_fin]
    rfl
  have halg : c⁻¹*((C/r^2)*(S^n*V)) = M/S^2 := by
    dsimp only [c,r,M]
    rw [div_pow]
    field_simp
    ring
  rw [← norm_iteratedFDeriv_one (f := fderiv ℝ w.value),norm_iteratedFDeriv_fderiv,hjet,
    iteratedFDeriv_const_smul_apply' (hG.of_le (by simp)).contDiffAt,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hc)]
  calc
    c⁻¹*‖iteratedFDeriv ℝ 2 G z‖ ≤ c⁻¹*((C/r^2)*(∫ y, |F y|)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hc.le)
    _ ≤ c⁻¹*((C/r^2)*(S^n*V)) := by
      rw [← hvolume]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFL1 (by positivity)) (inv_nonneg.mpr hc.le)
    _ = _ := halg

end RegularPointCoordinates

end

end OAI
