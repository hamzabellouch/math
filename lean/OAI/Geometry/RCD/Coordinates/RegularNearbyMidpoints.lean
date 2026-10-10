import OAI.Geometry.RCD.Transport.NearbyPlanCompression
import OAI.Geometry.RCD.Coordinates.RegularQuadraticMidpoints

namespace OAI

/-! # Actual nearby-endpoint paths with simultaneous distance midpoint laws -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hX in
theorem regular_nearby_midpoints (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) (p x y : ℕ → X) (z : ℕ → ℕ → X) (R : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 o)) (hz : ∀ i, Tendsto (z i) atTop (𝓝 o))
    (hR : ∀ k, 0 < R k) (hR0 : Tendsto R atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * R k)^2)
    (hx : ∀ k, dist (x k) (p k) ≤ R k/2)
    (hy : ∀ k, dist (y k) (p k) ≤ R k/2)
    (hzp : ∀ i k, dist (z i k) (p k) ≤ R k) :
    ∃ (η : ℕ → ℝ) (γ : ℕ → C(Time,X)), Tendsto η atTop (𝓝 0) ∧
      (∀ k, 0 < η k ∧ IsGeodesic (γ k) ∧
        dist (γ k 0) (x k) < η k * R k ∧ dist (γ k 1) (y k) < η k * R k ∧
        ∀ t : Time, dist (γ k t) (p k) ≤ 3 * R k) ∧
      ∀ i, Tendsto (fun k => fullMidpointDefect (z i k) (γ k)/(R k)^2) atTop (𝓝 0) := by
  let θ m := heatStep m/4
  have hθ m : 0 < θ m := div_pos (heatStep_pos m) (by norm_num)
  have hθle m : θ m ≤ 1/2 := by
    have hh : heatStep m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [θ]
    linarith
  have hθ0 : Tendsto θ atTop (𝓝 0) := by
    simpa only [zero_div] using heatStep_tendsto.div_const 4
  have hex m k := hX.nearby_endpoint_plan hn hK (hR k) (mul_pos (hθ m) (hR k))
    (by nlinarith [hθle m,hR k] : θ m * R k ≤ R k/2) (hx k) (hy k) (hcurv k)
  choose π hπ hg hopt hc he using hex
  let : ∀ m k, IsProbabilityMeasure (π m k) := hπ
  let B m k := ENNReal.ofReal (segmentCost n * (R k)^n /
    ((hausdorff n X).real (ball (p k) (R k)) * (θ m * R k)^n))
  have hends m i (_him : i ≤ m) k :
      (∀ᵐ w ∂(π m k).map (fun γ => γ 0), dist w (z i k) ≤ (1024 * R k)/512) ∧
      (∀ᵐ w ∂(π m k).map (fun γ => γ 1), dist w (z i k) ≤ (1024 * R k)/512) := by
    have hend : ∀ᵐ γ ∂π m k,
        dist (γ 0) (z i k) ≤ (1024 * R k)/512 ∧
        dist (γ 1) (z i k) ≤ (1024 * R k)/512 := by
      filter_upwards [he m k] with γ hγ
      have ht0 := dist_triangle4 (γ 0) (x k) (p k) (z i k)
      have ht1 := dist_triangle4 (γ 1) (y k) (p k) (z i k)
      rw [dist_comm (p k) (z i k)] at ht0 ht1
      have hsmall : θ m * R k ≤ R k/2 := by nlinarith [hθle m,hR k]
      constructor <;> linarith [hzp i k,hx k,hy k,hγ.1,hγ.2.1]
    constructor
    · apply (ae_map_iff (measurable_path_eval 0).aemeasurable measurableSet_closedBall).mpr
      exact hend.mono fun _ h => h.1
    · apply (ae_map_iff (measurable_path_eval 1).aemeasurable measurableSet_closedBall).mpr
      exact hend.mono fun _ h => h.2
  have hcompression m i (_him : i ≤ m) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      (B m k).toReal * (hausdorff n X).real (ball (z i k) (1024 * R k)) ≤ C :=
    hX.near_regular_compression_bound hn ho p (z i) R hp (hz i) hR hR0
      (by norm_num) (hθ m)
  let P m k (γ : C(Time,X)) :=
    dist (γ 0) (x k) < θ m * R k ∧ dist (γ 1) (y k) < θ m * R k ∧
      ∀ t : Time, dist (γ t) (p k) ≤ 3 * R k
  obtain ⟨d,γ,hd,hγ,hlim⟩ := hX.regular_quadratic_midpoint_selection hn hK ho z
    (fun _ k => 1024 * R k) hz (fun _ k => mul_pos (by norm_num) (hR k))
    (fun _ => by simpa using hR0.const_mul 1024) π hg hopt B
    (fun _ _ => ENNReal.ofReal_ne_top) hc hends hcompression P he
  refine ⟨fun k => θ (d k),γ,hθ0.comp hd,?_,?_⟩
  · intro k
    exact ⟨hθ (d k),(hγ k).2,(hγ k).1⟩
  · intro i
    have hh := (hlim i).mul_const ((1024:ℝ)^2)
    simp only [zero_mul] at hh
    apply hh.congr
    intro k
    field_simp [(hR k).ne']

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
