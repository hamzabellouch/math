import OAI.Probability.SLE.Angle.TargetDiskMass

namespace OAI

/-! Area transport for the disk Green weights at individual radius
levels. The derivative squared from area cancels the Green codimension
factor, leaving precisely the canonical mass weight. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma diskCompactPreimage_subset
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {K : Set ℂ} (hK : K ⊆ ball 0 1) :
    diskMapInv θ '' K ⊆ upperHalfPlane := by
  rintro z ⟨x,hx,rfl⟩
  exact diskMapInv_maps hθ (hK hx)

lemma diskCompactPreimage_compact (θ : ℝ)
    {K : Set ℂ} (hc : IsCompact K) (hK : K ⊆ ball 0 1) :
    IsCompact (diskMapInv θ '' K) := by
  apply hc.image_of_continuousOn
  change ContinuousOn (fun x : ℂ =>
    (Complex.exp (θ*Complex.I)-x*Complex.exp (-θ*Complex.I))/(1-x)) K
  exact (continuous_const.continuousOn.sub
    (continuous_id.mul continuous_const).continuousOn).div
    (continuous_const.sub continuous_id).continuousOn (fun x hx => disk_denominator_ne (hK hx))

theorem disk_level_integral_transport
    (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (K : Set ℂ) (hc : IsCompact K) (hK : K ⊆ ball 0 1)
    (g : ℂ → ℝ≥0∞) :
    (∫⁻ x in K, ENNReal.ofReal
      (‖deriv (diskMap θ) (diskMapInv θ x)‖^(-codimension κ))*g (diskMapInv θ x)) =
    ∫⁻ z in diskMapInv θ '' K,
      ENNReal.ofReal (‖deriv (diskMap θ) z‖^dimension κ)*g z := by
  have hs := diskCompactPreimage_subset hθ hK
  have hcomp := diskCompactPreimage_compact θ hc hK
  have himage : diskMap θ '' (diskMapInv θ '' K)=K := by
    ext x
    constructor
    · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
      simpa only [diskMap_diskMapInv hθ (hK hy)] using hy
    · intro hx
      exact ⟨diskMapInv θ x,⟨x,hx,rfl⟩,diskMap_diskMapInv hθ (hK hx)⟩
  have hd (z : ℂ) (hz : z ∈ diskMapInv θ '' K) := diskMap_hasDerivAt hθ (hs hz)
  conv_lhs => rw [← himage]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hcomp.measurableSet
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((diskMap_injOn hθ).mono hs)]
  apply setLIntegral_congr_fun hcomp.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _),
    diskMapInv_diskMap hθ (hs hz),← mul_assoc,← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [← (hd z hz).deriv,← Real.rpow_natCast,← Real.rpow_add (diskMap_deriv_pos hθ (hs hz))]
  congr 1
  unfold codimension dimension
  ring_nf

end SLEExactGauge.Target

end

end OAI
