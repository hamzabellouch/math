import OAI.Geometry.RCD.Metric.RescaledRootBounds
import OAI.Geometry.RCD.Sobolev.CenteredHarmonicEnergy

namespace OAI

/-! # Actual centered root directions, with their exact energy normalization -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_direction_data {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (u : Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (v : X → Euclidean (m+1)) (p : X) {r : ℝ} {d : ℕ}
    (hr : 0 < r) (hd : 6 ≤ d) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2)
    (A : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
    (hA : IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (hscale : ∀ j ≤ d, a*(3*((2 : ℝ)^j*r)) ≤ 1)
    (hframes : ∀ j ≤ d, ∃ (S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
      (w : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic p ((2 : ℝ)^j*r) κ
        (transformedColumn (hausdorff (m+1) X) hX.quadratic u S) w ∧
      IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u)
        (ball p ((2 : ℝ)^j*r)) measurableSet_ball S)
    (hv : ContinuousOn v (ball p ((2 : ℝ)^d*r)))
    (hrep : ∀ i, SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (u i) =ᵐ[
      (hausdorff (m+1) X).restrict (ball p ((2 : ℝ)^d*r))] fun x => v x i)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic
      (ball p ((2 : ℝ)^d*r)) (u i)) (z : Euclidean (m+1)) :
    ∃ w : SobolevSpace (hausdorff (m+1) X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic (ball p (5*r)) w ∧
      SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic w =ᵐ[
        (hausdorff (m+1) X).restrict (ball p (5*r))]
        (fun x => ⟪v x-v p,A z⟫_ℝ/r) ∧
      harmonicTargetNorm hX p (5*r) w ≤ 80*((m+1 : ℕ) : ℝ)*‖z‖ ∧
      ((hausdorff (m+1) X).real (ball p r))⁻¹*
        (∫ x in ball p r, r^2*localGamma (hausdorff (m+1) X) hX.quadratic w w x
          ∂hausdorff (m+1) X) = ‖z‖^2 ∧
      (fun x => r^2*localGamma (hausdorff (m+1) X) hX.quadratic w w x) =ᵐ[
        (hausdorff (m+1) X).restrict (ball p (5*r))]
        localGamma (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z))
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic u (A z)) := by
  let μ := hausdorff (m+1) X
  let U := sobolevColumnMap μ hX.quadratic u
  have hs₆ : ball p ((2 : ℝ)^6*r) ⊆ ball p ((2 : ℝ)^d*r) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hd) hr.le)
  have hs : ball p (5*r) ⊆ ball p ((2 : ℝ)^d*r) :=
    (ball_subset_ball (by norm_num; linarith : 5*r ≤ (2 : ℝ)^6*r)).trans hs₆
  have hb := (dyadic_root_rescaled_bounds m hm hX ha hBG u v p hr hκ hκ1 hsmall A hA 6
    (fun j hj => hscale j (hj.trans hd)) (fun j hj => hframes j (hj.trans hd))
    (hv.mono hs₆) (fun i => ae_restrict_of_ae_restrict_of_subset hs₆ (hrep i)) z
    (by norm_num : (0:ℝ)≤5) (by norm_num : (5:ℝ)<2^6/8)).1
  have hbound : ∀ x ∈ ball p (5*r),
      |⟪v x,A z⟫_ℝ-⟪v p,A z⟫_ℝ| ≤ (80*((m+1 : ℕ) : ℝ)*‖z‖)*r := by
    intro x hx
    have h := hb x hx.le
    simp only [abs_div,abs_of_pos hr] at h
    have hh := (div_le_iff₀ hr).mp h
    norm_num at hh
    calc
      _ = |⟪v x-v p,A z⟫_ℝ| := by rw [inner_sub_left]
      _ ≤ 2*((m : ℝ)+1)*8*‖z‖*5*r := hh
      _ = _ := by push_cast; ring
  have hU : SobolevSpace.toLp μ hX.quadratic (U (A z)) =ᵐ[μ.restrict (ball p (5*r))]
      fun x => ⟪v x,A z⟫_ℝ :=
    sobolevColumnMap_representative μ hX.quadratic u _ v
      (fun i => ae_restrict_of_ae_restrict_of_subset hs (hrep i)) (A z)
  have hUH : IsSobolevHarmonicOn μ hX.quadratic (ball p (5*r)) (U (A z)) :=
    (IsSobolevHarmonicOn.linearCombination μ hX.quadratic hu (A z)).mono μ hX.quadratic hs
  obtain ⟨w,hw,hwrep,hwnorm,hwe⟩ := hX.centered_harmonic_direction_with_energy hm p
    (mul_pos (by norm_num) hr) hr (by positivity) (U (A z)) (fun x => ⟪v x,A z⟫_ℝ)
    ⟪v p,A z⟫_ℝ hUH hU hbound
  have he := rescaled_local_pairing_of_centering μ hX.quadratic (ball p (5*r)) hr.ne'
    (U (A z)) (U (A z)) w w hwe hwe
  refine ⟨w,hw,by simpa only [inner_sub_left] using hwrep,hwnorm,?_,he⟩
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : r≤5*r)) he)]
  rw [← sobolevMeanGram_inner μ hX.quadratic U (ball p r) measurableSet_ball,
    real_inner_comm,meanGram_energy_of_exact_normalization μ hX.quadratic U
      (ball p r) measurableSet_ball A hA,A.symm_apply_apply]

end RegularPointCoordinates

end

end OAI
