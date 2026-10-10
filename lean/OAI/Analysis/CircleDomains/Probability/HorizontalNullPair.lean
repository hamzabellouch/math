import OAI.Analysis.CircleDomains.Probability.NullPairFromLevels

namespace OAI

/-! The companion trace pair with the ordinary horizontal coordinate.
The same proved level argument applies to the constant rotated homeomorphism. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def horizontalLinear : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp euclideanPlaneCoordinates.toContinuousLinearMap

 @[simp] theorem horizontalLinear_apply (p : EuclideanPlane) : horizontalLinear p = p 0 := rfl

 def horizontalGradient (_ : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun i => if i = 0 then 1 else 0)

 theorem horizontal_weak_gradient :
    DeGiorgi.HasWeakGrad horizontalGradient (Complex.re ∘ complexPlaneCoordinates) univ := by
  intro i
  have h := weakPartial_of_smooth_on isOpen_univ horizontalLinear.contDiff.contDiffOn i
  convert h using 1
  · funext p
    fin_cases i <;> simp [horizontalGradient, ContinuousLinearMap.fderiv, horizontalLinear_apply]
  · rfl

 theorem horizontal_gradient_memLp (R : ℝ) (i : Fin 2) :
    MemLp (fun p => horizontalGradient p i) 2 (volume.restrict (ball 0 R)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  fin_cases i
  · exact memLp_const 1
  · exact memLp_const 0

 theorem horizontal_as_height :
    TendstoLocallyUniformly
      (fun (_ : ℕ) z => (Homeomorph.mulLeft₀ Complex.I Complex.I_ne_zero z).im) Complex.re atTop := by
  have h : TendstoLocallyUniformly (fun (_ : ℕ) z => z.re) Complex.re atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      (tendsto_const_nhds (x := (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ))))
  change TendstoLocallyUniformly (fun (_ : ℕ) z => (Complex.I*z).im) Complex.re atTop
  simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using h

 theorem sobolev_horizontal_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), W.weakGrad p = 0) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), z.re)) '' F) = 0 := by
  apply null_pair_image_of_null_level_images hF
    (hU.comp complexPlaneCoordinates.symm.continuous) Complex.continuous_re
  exact sobolev_coordinate_level_null_image hcoarea
    (fun _ => Homeomorph.mulLeft₀ Complex.I Complex.I_ne_zero) Complex.continuous_re
    horizontal_as_height horizontal_weak_gradient horizontal_gradient_memLp hF hQ hFQ hU W
    (hz.mono (fun _ hp => Or.inr hp))

end CircleDomainRigidity

end

end OAI
