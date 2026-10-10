import OAI.Geometry.RCD.Heat.FirstOrderHeatCoefficientPaths
import OAI.Geometry.RCD.Heat.FirstOrderHeatVelocityError
import OAI.Geometry.RCD.Harmonic.FirstOrderPathVelocity
import OAI.Geometry.RCD.Coordinates.FramePathNormalizedEndpoint

namespace OAI

/-! # Quantitative scalar endpoints along actual controlled heat paths -/

open Set Filter MeasureTheory Metric Finset
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_heat_endpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) ((π k).map (fun γ => (γ 0,γ 1))))
    {B : ℝ} (hB : 0≤B)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤
      ENNReal.ofReal (B/(hausdorff n X).real (ball (p k) (4*r k))) • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k)≤r k/12)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k)≤r k/12)
    {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L a : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |h k x|≤A k) (hscale : ∀ k, (A k:ℝ)≤a*r k)
    (P : ℕ → C(Time,X) → Prop) (hP : ∀ k, ∀ᵐ γ ∂π k, P k γ) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hk k := hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)
    let φ k := kernelHeat μ Q (hk k) (η*(r k)^2) (h k)
    ∃ (γ : ℕ → C(Time,X)) (e z : ℕ → ℝ),
      (∀ k, P k (γ k)) ∧ (∀ k, IsGeodesic (γ k)) ∧
      (∀ k (t : Time), dist (γ k t) (p k)≤r k/4) ∧
      (∀ k, 0≤e k) ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ k, 0≤z k) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ k, |φ k (γ k 1)-φ k (γ k 0)|/r k≤
        Real.sqrt (((L:ℝ)*Real.exp (-K*(η*(r k)^2)))^2+e k)*
          (dist (v k (γ k 0)) (v k (γ k 1))/r k)+z k+Real.sqrt (e k) := by
  intro μ Q hk φ
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hs (k : ℕ) : 0<η*(r k)^2 := mul_pos hη (sq_pos_of_pos (hr k))
  let w k := heatSobolev μ Q (η*(r k)^2) (hs k) (h k)
  let E k := frameVelocityError μ Q (u k) (w k)
  have hw (k : ℕ) : SobolevSpace.toLp μ Q (w k) =ᵐ[μ] φ k := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q (hk k) (hs k) (h k)).symm
  have hφ (k : ℕ) : Continuous (φ k) :=
    (hX.kernelHeat_bounded_regularity hn (p k) (hk k) (h k) (A k) (hA k) _ (hs k)).1.continuous
  have hgrad (k : ℕ) : ∀ᵐ x ∂μ,
      localGamma μ Q (w k) (w k) x≤((L:ℝ)*Real.exp (-K*(η*(r k)^2)))^2 := by
    filter_upwards [hX.heat_compact_slope_bdd K n hn (hV k) (hVc k) (p k) (h k) (hrep k) _ (hs k),
      localGamma_self μ Q (w k),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q (w k))] with x hx he hn
    rw [he]
    exact pow_le_pow_left₀ hn hx 2
  obtain ⟨hEI,hE0⟩ := hX.first_order_heat_velocity_error hn hK p r ε hr hcurv hε hε1 hε0
    u v hsplit hη hη1 h V L A hV hVc hrep hA
  have hbounded (k : ℕ) := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
    ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
    (show 0≤r k/12 by linarith [hr k]) (hs₀ k) (hs₁ k)
  have hstay (k : ℕ) : ∀ᵐ γ ∂π k, ∀ t : Time, γ t∈ball (p k) (r k) := by
    filter_upwards [hbounded k] with γ hγ t
    exact (hγ.2 t).trans_lt (by linarith [hr k])
  have hstay' (k : ℕ) (t : Time) : ∀ᵐ x ∂(π k).map (fun γ => γ t), x∈ball (p k) (r k) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [hstay k] with γ hγ
    exact hγ t
  have hi (k : ℕ) := (compressed_segment_integral μ (π k) ENNReal.ofReal_ne_top (hcomp k)
    (hstay' k) (hEI k) (Eventually.of_forall (frameVelocityError_nonneg μ Q (u k) (w k)))).2.1
  have hg (k : ℕ) := testPlan_eval_property_on μ (π k) (hcomp k) measurableSet_ball (hstay k)
    (ae_restrict_of_ae (hgrad k))
  have hv (k : ℕ) := hX.first_order_path_velocity hn (hr k) (hε k) (hε1 k) (u k) (v k)
    (hsplit k) (w k) (φ k) (hφ k) (hw k) (π k) (hgeo k) (hopt k) ENNReal.ofReal_ne_top
    (hcomp k) (hs₀ k) (hs₁ k)
  let R k γ := P k γ ∧
    (AbsolutelyContinuousOnInterval (fun t => φ k (geodesicExtension γ t)) 0 1 ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t => v k (geodesicExtension γ t) i) 0 1) ∧
      ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
        (deriv (fun s => φ k (geodesicExtension γ s)) t-
          ∑ i, localGamma μ Q (u k i) (w k) (geodesicExtension γ t)*
            deriv (fun s => v k (geodesicExtension γ s) i) t)^2≤
          (dist (γ 0) (γ 1))^2*E k (geodesicExtension γ t)) ∧
    IntegrableOn (fun t => E k (geodesicExtension γ t)) (Icc (0:ℝ) 1) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      localGamma μ Q (w k) (w k) (geodesicExtension γ t)≤((L:ℝ)*Real.exp (-K*(η*(r k)^2)))^2)
  have hR (k : ℕ) : ∀ᵐ γ ∂π k, R k γ := (hP k).and ((hv k).and ((hi k).and (hg k)))
  obtain ⟨γ,b,α,hRγ,hγ,hstayγ,hα,hα0,haff,hb,hbe,he0,hz0⟩ :=
    hX.first_order_heat_coefficient_paths hn hK p r ε hr hr0 hcurv hε hε1 hε0 u v hsplit
      π hgeo hopt hB hcomp hs₀ hs₁ hη hη1 h V L a A hV hVc hrep hA hscale E
      (fun k => frameVelocityError_nonneg μ Q (u k) (w k)) hEI hE0 R hR
  let e k := ∫ t in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) t)
  let z k := α k*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b k i) t|)
  refine ⟨γ,e,z,fun k => (hRγ k).1,hγ,hstayγ,
    fun k => integral_nonneg (fun _ => frameVelocityError_nonneg μ Q (u k) (w k) _),he0,
    fun k => mul_nonneg (hα k) (sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))),hz0,?_⟩
  intro k
  have hspeed : dist (γ k 0) (γ k 1)≤r k := by
    have hh := dist_triangle (γ k 0) (p k) (γ k 1)
    rw [dist_comm (p k) (γ k 1)] at hh
    linarith [hstayγ k 0,hstayγ k 1,hr k]
  exact frame_path_normalized_endpoint μ Q (u k) (w k) (γ k) (b k) (v k) (φ k)
    (hr k) hspeed (hRγ k).2.1.1 (hb k) (hRγ k).2.1.2.1 (haff k) (hbe k)
    (hRγ k).2.2.2 (hRγ k).2.2.1 (hRγ k).2.1.2.2

end RegularPointCoordinates

end

end OAI
