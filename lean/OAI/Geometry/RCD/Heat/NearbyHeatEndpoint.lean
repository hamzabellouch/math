import OAI.Geometry.RCD.Heat.FirstOrderHeatEndpoint
import OAI.Geometry.RCD.Coordinates.NearbyNormalizedPlan
import OAI.Geometry.RCD.Coordinates.VanishingDiagonalCost

namespace OAI

/-! # Shrinking nearby endpoints retaining the actual heat estimate -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.nearby_heat_endpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48)
    {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L a : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ z ∂hausdorff n X, |h k z|≤A k) (hscale : ∀ k, (A k:ℝ)≤a*r k) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hk k := hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)
    let φ k := kernelHeat μ Q (hk k) (η*(r k)^2) (h k)
    ∃ (γ : ℕ → C(Time,X)) (δ e z : ℕ → ℝ),
      (∀ k, 0<δ k ∧ δ k≤1/2) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ k, IsGeodesic (γ k)) ∧
      (∀ k, dist (γ k 0) (x k)<δ k*r k/24 ∧ dist (γ k 1) (y k)<δ k*r k/24) ∧
      (∀ k (t : Time), dist (γ k t) (p k)≤r k/4) ∧
      (∀ k, 0≤e k) ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ k, 0≤z k) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ k, |φ k (γ k 1)-φ k (γ k 0)|/r k≤
        Real.sqrt (((L:ℝ)*Real.exp (-K*(η*(r k)^2)))^2+e k)*
          (dist (v k (γ k 0)) (v k (γ k 1))/r k)+z k+Real.sqrt (e k) := by
  intro μ Q hk φ
  classical
  obtain ⟨D,hD,hplans⟩ := hX.nearby_normalized_plan hn hK
  let δ (m : ℕ) : ℝ := ((m:ℝ)+2)⁻¹
  have hδ (m : ℕ) : 0<δ m ∧ δ m≤1/2 := by
    refine ⟨by dsimp only [δ]; positivity,?_⟩
    rw [one_div]
    change ((m:ℝ)+2)⁻¹≤(2:ℝ)⁻¹
    exact inv_anti₀ (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  choose π hπ hgeo hopt hcomp hends using fun m k =>
    hplans (hr k) (hcurv k) (hδ m).1 (hδ m).2 (hx k) (hy k)
  let (m k : ℕ) : IsProbabilityMeasure (π m k) := hπ m k
  let B (m : ℕ) := D/(δ m)^n
  have hB (m : ℕ) : 0≤B m := div_nonneg hD.le (pow_pos (hδ m).1 n).le
  have hstart (m k : ℕ) : ∀ᵐ z ∂(π m k).map (fun γ => γ 0), dist z (p k)≤r k/12 := by
    apply (ae_map_iff (measurable_path_eval 0).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends m k] with γ he
    have hh := dist_triangle (γ 0) (x k) (p k)
    nlinarith [hx k,(hδ m).2,hr k]
  have hfinish (m k : ℕ) : ∀ᵐ z ∂(π m k).map (fun γ => γ 1), dist z (p k)≤r k/12 := by
    apply (ae_map_iff (measurable_path_eval 1).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends m k] with γ he
    have hh := dist_triangle (γ 1) (y k) (p k)
    nlinarith [hy k,(hδ m).2,hr k]
  have hrow (m : ℕ) := hX.first_order_heat_endpoint hn hK p r ε hr hr0 hcurv hε hε1 hε0
    u v hsplit (π m) (hgeo m) (hopt m) (hB m) (hcomp m) (hstart m) (hfinish m)
    hη hη1 h V L a A hV hVc hrep hA hscale
    (fun k γ => dist (γ 0) (x k)<δ m*r k/24 ∧ dist (γ 1) (y k)<δ m*r k/24)
    (fun k => (hends m k).mono (fun _ he => ⟨he.1,he.2.1⟩))
  choose γ e z hnear hγ hstay he he0 hz hz0 hbound using hrow
  obtain ⟨d,hd,hcost⟩ := exists_vanishing_diagonal_cost (fun m k => e m k+z m k)
    (fun m k => add_nonneg (he m k) (hz m k)) (fun m => by simpa only [add_zero] using (he0 m).add (hz0 m))
  have hediag : Tendsto (fun k => e (d k) k) atTop (𝓝 0) :=
    squeeze_zero (fun k => he (d k) k) (fun k => le_add_of_nonneg_right (hz (d k) k)) hcost
  have hzdiag : Tendsto (fun k => z (d k) k) atTop (𝓝 0) :=
    squeeze_zero (fun k => hz (d k) k) (fun k => le_add_of_nonneg_left (he (d k) k)) hcost
  have hδ0 : Tendsto (fun k => δ (d k)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hd))
  exact ⟨fun k => γ (d k) k,fun k => δ (d k),fun k => e (d k) k,fun k => z (d k) k,
    fun k => hδ (d k),hδ0,fun k => hγ (d k) k,fun k => hnear (d k) k,
    fun k => hstay (d k) k,fun k => he (d k) k,hediag,fun k => hz (d k) k,hzdiag,
    fun k => hbound (d k) k⟩

end RegularPointCoordinates

end

end OAI
