import OAI.Geometry.RCD.Coordinates.FirstOrderHeatFrameEnergy
import OAI.Geometry.RCD.Harmonic.FirstOrderCoefficientPaths

namespace OAI

/-! # Controlled paths for the actual heat pairings of the original coordinates -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.first_order_heat_coefficient_paths {K : ℝ} {n : ℕ}
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
    (E : ℕ → X → ℝ) (hE : ∀ k x, 0≤E k x)
    (hEI : ∀ k, IntegrableOn (E k) (ball (p k) (r k)) (hausdorff n X))
    (hE0 : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (4*r k)))⁻¹*
      ∫ x in ball (p k) (r k), E k x ∂hausdorff n X) atTop (𝓝 0))
    (P : ℕ → C(Time,X) → Prop) (hP : ∀ k, ∀ᵐ γ ∂π k, P k γ) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hs (k : ℕ) : 0<η*(r k)^2 := mul_pos hη (sq_pos_of_pos (hr k))
    let w k := heatSobolev μ Q (η*(r k)^2) (hs k) (h k)
    ∃ (γ : ℕ → C(Time,X)) (b : ℕ → Fin n → ℝ → ℝ) (α : ℕ → ℝ),
      (∀ k, P k (γ k)) ∧ (∀ k, IsGeodesic (γ k)) ∧
      (∀ k (t : Time), dist (γ k t) (p k)≤r k/4) ∧
      (∀ k, 0≤α k) ∧ Tendsto α atTop (𝓝 0) ∧
      (∀ k i (t : Time),
        |(v k (γ k t) i-((1-(t:ℝ))*v k (γ k 0) i+(t:ℝ)*v k (γ k 1) i))/r k|≤α k) ∧
      (∀ k i, AbsolutelyContinuousOnInterval (b k i) 0 1) ∧
      (∀ k i, b k i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
        fun t => localGamma μ Q (u k i) (w k) (geodesicExtension (γ k) t)) ∧
      Tendsto (fun k => ∫ t in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) t)) atTop (𝓝 0) ∧
      Tendsto (fun k => α k*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b k i) t|)) atTop (𝓝 0) := by
  intro μ Q hs w
  obtain ⟨M,G,_hM,hG,hGE⟩ := hX.first_order_heat_frame_energy hn hK p r ε hr hcurv hε hε1
    u v hsplit hη hη1 h V L a A hV hVc hrep hA hscale
  have hstay (k : ℕ) : ∀ᵐ γ ∂π k, ∀ t : Time, γ t∈ball (p k) (4*r k) := by
    have hb := optimal_geodesic_plan_bounded ((π k).map (fun γ => γ 0))
      ((π k).map (fun γ => γ 1)) (π k) (hgeo k) (hopt k) (p k)
      (show 0≤r k/12 by linarith [hr k]) (hs₀ k) (hs₁ k)
    filter_upwards [hb] with γ hγ t
    exact (hγ.2 t).trans_lt (by linarith [hr k])
  have hpair (k : ℕ) (i : Fin n) := testPlan_eval_property_on μ (π k) (hcomp k) measurableSet_ball
    (hstay k) (show ∀ᵐ x ∂μ.restrict (ball (p k) (4*r k)),
      SobolevSpace.toLp μ Q (G k i) x=localGamma μ Q (u k i) (w k) x from hG k i)
  let R k γ := P k γ ∧ ∀ i, (fun t => SobolevSpace.toLp μ Q (G k i) (geodesicExtension γ t))
    =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => localGamma μ Q (u k i) (w k) (geodesicExtension γ t)
  have hR (k : ℕ) : ∀ᵐ γ ∂π k, R k γ := (hP k).and (ae_all_iff.mpr (hpair k))
  obtain ⟨γ,b,α,hRγ,hγ,hstayγ,hα,hαlim,haff,hb,hbG,hElim,hprod⟩ :=
    hX.first_order_coefficient_paths hn hK p r ε hr hr0 hcurv hε hε1 hε0 u v hsplit
      π hgeo hopt hB hcomp hs₀ hs₁ G hGE E hE hEI hE0 R hR
  refine ⟨γ,b,α,fun k => (hRγ k).1,hγ,hstayγ,hα,hαlim,haff,hb,?_,hElim,hprod⟩
  intro k i
  exact (hbG k i).trans ((hRγ k).2 i)

end RegularPointCoordinates

end

end OAI
