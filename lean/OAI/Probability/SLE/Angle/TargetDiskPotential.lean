import OAI.Probability.SLE.Angle.TargetClockIdentification
import OAI.Probability.SLE.Angle.TargetDiskRadius
import OAI.Probability.SLE.Geometry.RestartGreenIntegral

namespace OAI

/-! The prescribed disk potential is exactly the conformally weighted
current Green mass of the compact disk preimage. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def diskSourceCompact (θ : ℝ) : Set ℂ := diskMapInv θ '' diskK

lemma diskK_subset_unit : diskK ⊆ ball (0:ℂ) 1 := by
  intro x hx
  exact (closedBall_subset_ball (by norm_num : (1:ℝ)/4<1)) hx

lemma diskSourceCompact_subset {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    diskSourceCompact θ ⊆ upperHalfPlane := by
  rintro z ⟨x,hx,rfl⟩
  exact diskMapInv_maps hθ (diskK_subset_unit hx)

lemma diskSourceCompact_compact (θ : ℝ) : IsCompact (diskSourceCompact θ) := by
  change IsCompact (diskMapInv θ '' closedBall (0:ℂ) (1/4))
  apply (isCompact_closedBall (0:ℂ) (1/4)).image_of_continuousOn
  change ContinuousOn (fun x : ℂ =>
    (Complex.exp (θ*Complex.I)-x*Complex.exp (-θ*Complex.I))/(1-x)) _
  apply ContinuousOn.div
  · exact continuous_const.continuousOn.sub (continuous_id.mul continuous_const).continuousOn
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro x hx
    exact disk_denominator_ne (diskK_subset_unit hx)

lemma diskSourceCompact_image {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    diskMap θ '' diskSourceCompact θ=diskK := by
  ext x
  constructor
  · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
    simpa only [diskMap_diskMapInv hθ (diskK_subset_unit hy)] using hy
  · intro hx
    exact ⟨diskMapInv θ x,⟨x,hx,rfl⟩,diskMap_diskMapInv hθ (diskK_subset_unit hx)⟩

lemma diskMap_deriv_pos {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : 0<‖deriv (diskMap θ) z‖ := by
  rw [diskMap_deriv_norm hθ hz]
  exact div_pos (mul_pos (by norm_num) (disk_center_height hθ))
    (sq_pos_of_pos (norm_pos_iff.mpr (diskMap_denominator_ne hθ hz)))

theorem potential_eq_source_green_integral
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (T : ℝ≥0) :
    potential κ θ b (κ*T) =
      ∫⁻ z in diskSourceCompact θ,
        ENNReal.ofReal (‖deriv (diskMap θ) z‖^dimension κ) *
          ENNReal.ofReal (greenDensity κ U γ G T z) := by
  have hK := diskSourceCompact_compact θ
  have hsub := diskSourceCompact_subset hθ
  have hd (z : ℂ) (hz : z ∈ diskSourceCompact θ) := diskMap_hasDerivAt hθ (hsub hz)
  rw [potential,← diskSourceCompact_image hθ,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK.measurableSet
      (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      ((diskMap_injOn hθ).mono hsub)]
  apply setLIntegral_congr_fun hK.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _),
    green_eq_transported_density κ hκ b U hUc γ G F hw hU θ (diskMap θ z) T,
    diskMapInv_diskMap hθ (hsub hz),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [← (hd z hz).deriv,← Real.rpow_natCast,
    ← Real.rpow_add (diskMap_deriv_pos hθ (hsub hz))]
  congr 1
  simp only [codimension,dimension]
  ring

end SLEExactGauge.Target

end

end OAI
