import OAI.Geometry.RCD.Transport.MetricLocalMidpointVolume
import OAI.Geometry.RCD.Metric.MetricLawMass

namespace OAI

/-! # The midpoint contraction for the actual normalized metric laws -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem pointed_inner_preimage_eq {n : ℕ} {p : X} {r S ρ ε a : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hρS : ρ < S)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    (z : Euclidean n) (hz : ‖z‖+a+2*ε ≤ ρ) :
    V ⁻¹' closedBall z a ∩ closedBall p (ρ*r) =
      V ⁻¹' closedBall z a ∩ ball p (S*r) := by
  ext u
  constructor
  · rintro ⟨hu,hrho⟩
    exact ⟨hu,hrho.trans_lt (mul_lt_mul_of_pos_right hρS hr)⟩
  · rintro ⟨hu,hball⟩
    refine ⟨hu,?_⟩
    have hv := (abs_le.mp (pointed_radial_distance hr hS hV hball.le)).1
    have hdist : ‖V u-z‖ ≤ a := by
      simpa only [mem_preimage,mem_closedBall,dist_eq_norm] using hu
    have hnorm : ‖V u‖ ≤ a+‖z‖ := by
      have hh := norm_add_le (V u-z) z
      simp only [sub_add_cancel] at hh
      linarith
    change dist u p ≤ ρ*r
    apply (div_le_iff₀ hr).mp
    linarith

theorem NoncollapsedRCD.metric_local_midpoint_law {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {r S ρ η ε a b : ℝ}
    (hr : 0 < r) (hS : 0 < S) (hρ : 0 ≤ ρ) (hρS : ρ < S) (hε : 0 ≤ ε)
    (hroom : ρ+2*η+ε < S)
    (V : X → Euclidean n) (hVm : Measurable V)
    (hV : IsPointedApproximation p 0 r S ε V) (x y z : Euclidean n)
    (hx : closedBall x a ⊆ closedBall z η) (hy : closedBall y b ⊆ closedBall z η)
    (hxa : ‖x‖+a+2*ε ≤ ρ) (hyb : ‖y‖+b+2*ε ≤ ρ)
    (hA0 : hausdorff n X (V ⁻¹' closedBall x a ∩ ball p (S*r)) ≠ 0)
    (hB0 : hausdorff n X (V ⁻¹' closedBall y b ∩ ball p (S*r)) ≠ 0)
    (hfin : hausdorff n X (ball p (S*r)) ≠ ⊤) :
    let P := (normalizedBallPushforward (hausdorff n X) p r S V hfin : Measure (Euclidean n))
    (midpointFloor K n (2*ρ*r)).toReal^n * P.real (closedBall y b) ≤
      P.real (closedBall ((1/2:ℝ) • (x+y))
        ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε))))) := by
  let μ := hausdorff n X
  have heA := pointed_inner_preimage_eq hr hS.le hρS hV x hxa
  have heB := pointed_inner_preimage_eq hr hS.le hρS hV y hyb
  have hm := hX.metric_local_midpoint_volume hn hr hρ hρS.le hε hroom.le V hVm hV
    x y z hx hy (by rwa [heA]) (by rwa [heB])
  dsimp only at hm
  have hp := midpoint_root_bound_to_mass (by omega : 0 < n) hm
  let C := V ⁻¹' closedBall ((1/2:ℝ) • (x+y))
    ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) ∩ closedBall p ((ρ+2*η+ε)*r)
  have hCfin : μ C ≠ ⊤ :=
    (hX.finiteOnBounded C (isBounded_closedBall.subset inter_subset_right)).ne
  have hpr := ENNReal.toReal_mono hCfin hp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,heB] at hpr
  have hCsub : C ⊆ V ⁻¹' closedBall ((1/2:ℝ) • (x+y))
      ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) ∩ ball p (S*r) := by
    intro u hu
    exact ⟨hu.1,hu.2.trans_lt (mul_lt_mul_of_pos_right hroom hr)⟩
  have hCmono := measureReal_mono hCsub
    (ne_of_lt ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hfin)))
  have hpos : 0 < μ.real (ball p (S*r)) :=
    ENNReal.toReal_pos (hX.fullSupport p (S*r) (mul_pos hS hr)).ne' hfin
  dsimp only
  rw [normalizedBallPushforward_real μ p r S V hfin hpos hVm measurableSet_closedBall,
    normalizedBallPushforward_real μ p r S V hfin hpos hVm measurableSet_closedBall]
  have hs := mul_le_mul_of_nonneg_left (hpr.trans hCmono) (inv_nonneg.mpr hpos.le)
  simpa only [μ,Measure.real,mul_left_comm] using hs

end RegularPointCoordinates

end

end OAI
