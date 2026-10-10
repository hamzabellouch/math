import OAI.Geometry.RCD.Transport.MetricSetMidpointVolume
import OAI.Geometry.RCD.Transport.MetricLocalMidpointLaw

namespace OAI

/-! # Both endpoint masses in the normalized metric-law midpoint bound -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem pointed_inner_set_preimage_eq {n : ℕ} {p : X} {r S ρ ε : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hρS : ρ < S)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    {A : Set (Euclidean n)} (hA : ∀ z ∈ A, ‖z‖+2*ε ≤ ρ) :
    V ⁻¹' A ∩ closedBall p (ρ*r) = V ⁻¹' A ∩ ball p (S*r) := by
  ext x
  constructor
  · rintro ⟨hx,hρ⟩
    exact ⟨hx,hρ.trans_lt (mul_lt_mul_of_pos_right hρS hr)⟩
  · rintro ⟨hx,hball⟩
    refine ⟨hx,?_⟩
    have hv := (abs_le.mp (pointed_radial_distance hr hS hV hball.le)).1
    exact (div_le_iff₀ hr).mp (by linarith only [hv,hA (V x) hx])

theorem NoncollapsedRCD.metric_set_midpoint_law {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {r S ρ η ε : ℝ} (hr : 0 < r) (hS : 0 < S) (hρ : 0 ≤ ρ) (hρS : ρ < S)
    (he : 0 ≤ ε) (hroom : ρ+2*η+ε < S)
    (V : X → Euclidean n) (hVm : Measurable V) (hV : IsPointedApproximation p 0 r S ε V)
    {A B : Set (Euclidean n)} (hA : MeasurableSet A) (hB : MeasurableSet B) (z : Euclidean n)
    (hAsub : A ⊆ closedBall z η) (hBsub : B ⊆ closedBall z η)
    (hAnorm : ∀ a ∈ A, ‖a‖+2*ε ≤ ρ) (hBnorm : ∀ b ∈ B, ‖b‖+2*ε ≤ ρ)
    (hA0 : hausdorff n X (V ⁻¹' A ∩ ball p (S*r)) ≠ 0)
    (hB0 : hausdorff n X (V ⁻¹' B ∩ ball p (S*r)) ≠ 0)
    (hfin : hausdorff n X (ball p (S*r)) ≠ ⊤) :
    let P := (normalizedBallPushforward (hausdorff n X) p r S V hfin : Measure (Euclidean n))
    (2*midpointFloor K n (2*ρ*r)).toReal^n*min (P.real A) (P.real B) ≤
      P.real (cthickening (Real.sqrt (2*(ε*(4*ρ+ε)))) (midpointSet A B)) := by
  let μ := hausdorff n X
  have heA := pointed_inner_set_preimage_eq hr hS.le hρS hV hAnorm
  have heB := pointed_inner_set_preimage_eq hr hS.le hρS hV hBnorm
  have hm := hX.metric_set_midpoint_volume hn hr hρ hρS.le he hroom.le V hVm hV hA hB z
    hAsub hBsub (by rwa [heA]) (by rwa [heB])
  let C := V ⁻¹' cthickening (Real.sqrt (2*(ε*(4*ρ+ε)))) (midpointSet A B) ∩
    closedBall p ((ρ+2*η+ε)*r)
  have hCfin : μ C ≠ ⊤ := (hX.finiteOnBounded C (isBounded_closedBall.subset inter_subset_right)).ne
  have hA_fin : μ (V ⁻¹' A ∩ ball p (S*r)) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right hfin
  have hB_fin : μ (V ⁻¹' B ∩ ball p (S*r)) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right hfin
  have hmin : (min (μ (V ⁻¹' A ∩ ball p (S*r))) (μ (V ⁻¹' B ∩ ball p (S*r)))).toReal =
      min (μ.real (V ⁻¹' A ∩ ball p (S*r))) (μ.real (V ⁻¹' B ∩ ball p (S*r))) := by
    dsimp only [Measure.real]
    rcases le_total (μ (V ⁻¹' A ∩ ball p (S*r))) (μ (V ⁻¹' B ∩ ball p (S*r))) with h | h
    · rw [min_eq_left h,min_eq_left (ENNReal.toReal_mono hB_fin h)]
    · rw [min_eq_right h,min_eq_right (ENNReal.toReal_mono hA_fin h)]
  dsimp only [μ] at hmin
  have hp := ENNReal.toReal_mono hCfin hm
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,heA,heB,hmin] at hp
  have hCsub : C ⊆ V ⁻¹' cthickening (Real.sqrt (2*(ε*(4*ρ+ε)))) (midpointSet A B) ∩ ball p (S*r) := by
    intro x hx
    exact ⟨hx.1,hx.2.trans_lt (mul_lt_mul_of_pos_right hroom hr)⟩
  have hCmono := measureReal_mono hCsub (measure_ne_top_of_subset inter_subset_right hfin)
  have hpos : 0 < μ.real (ball p (S*r)) :=
    ENNReal.toReal_pos (hX.fullSupport p (S*r) (mul_pos hS hr)).ne' hfin
  dsimp only
  rw [normalizedBallPushforward_real μ p r S V hfin hpos hVm hA,
    normalizedBallPushforward_real μ p r S V hfin hpos hVm hB,
    normalizedBallPushforward_real μ p r S V hfin hpos hVm isClosed_cthickening.measurableSet]
  have hs := mul_le_mul_of_nonneg_left (hp.trans hCmono) (inv_nonneg.mpr hpos.le)
  rw [← mul_min_of_nonneg _ _ (inv_nonneg.mpr hpos.le)]
  simp only [ENNReal.toReal_mul]
  convert hs using 1
  ring

end RegularPointCoordinates

end

end OAI
