import OAI.Geometry.RCD.Transport.PointwiseReduced
import OAI.Geometry.RCD.Sobolev.GeometricMeanSum
import OAI.Geometry.RCD.Transport.PlanLogDensity

namespace OAI

/-! # The finite-dimensional Gaussian midpoint entropy-power bound

The pointwise reduced density bound, the published Gaussian lower bound for
its coefficient, and the two-term logarithmic integral inequality give the
midpoint estimate on the prescribed compressed optimal dynamical plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem gaussian_midpoint_entropy_power (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    : Real.exp (K*(wassersteinSq a.left a.right).toReal/(8*N))*
        (Real.exp (-(boltzmannEntropy (hausdorff n X) a.left)/N)+
          Real.exp (-(boltzmannEntropy (hausdorff n X) a.right)/N))/2 ≤
      Real.exp (-(boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ midpointTime)))/N) := by
  let μ := hausdorff n X
  let r := fun (s : Time) (γ : C(Time,X)) => (π.map (fun γ => γ s)).rnDeriv μ (γ s)
  let L := fun (s : Time) (γ : C(Time,X)) => Real.log ((r s γ)^(-(1/N))).toReal
  let w := fun γ : C(Time,X) => K*dist (γ 0) (γ 1)^2/(8*N)
  have hN1 : 1 < N := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN0 : N ≠ 0 := by linarith
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x a.center ≤ a.radius := by rw [he.1]; exact a.left_support
  have hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x a.center ≤ a.radius := by rw [he.2]; exact a.right_support
  have hd := a.distance_bound π inferInstance hg hp
  have hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π := by
    apply Integrable.mono' (integrable_const (a.distance^2))
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).pow_const 2).aestronglyMeasurable
    exact hd.mono fun γ hγ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ dist_nonneg hγ _
  have hL (s : Time) : Integrable (L s) π ∧
      (∫ γ, L s γ ∂π)=-(boltzmannEntropy μ (π.map (fun γ => γ s)))/N :=
    bounded_plan_log_density μ a.center a.radius_nonneg π hg hpp (show 0 < (C:ℝ) from hC)
      hc hs₀ hs₁ N s
  have hw : Integrable w π := (hi.const_mul K).div_const (8*N)
  have hpow (s : Time) : ∀ᵐ γ ∂π, (r s γ)^(-(1/N)) ≠ 0 ∧ (r s γ)^(-(1/N)) ≠ ∞ := by
    have ha := Measure.absolutelyContinuous_of_le_smul (hc s)
    have hpull := ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.rnDeriv_pos ha).and (ha.ae_le (Measure.rnDeriv_lt_top (π.map (fun γ => γ s)) μ)))
    filter_upwards [hpull] with γ hγ
    exact ⟨(ENNReal.rpow_pos hγ.1 hγ.2.ne).ne',ENNReal.rpow_ne_top_of_ne_zero hγ.1.ne' hγ.2.ne⟩
  have hcoef (d : ℝ) (hd : 0 ≤ d) :
      ENNReal.ofReal (Real.exp (K*d^2/(8*N))/2) ≤ sigma K (N+1) (1/2) d := by
    have hh := sigma_signed_gaussian_lower K (N+1) d (1/2) (by linarith) hd (by norm_num) (by norm_num)
    have hx : K*d^2*(1-(1/2:ℝ)^2)/(6*((N+1)-1))=K*d^2/(8*N) := by
      field_simp [hN0]; ring
    rw [hx] at hh
    convert hh using 1
    congr 1
    ring
  have hpw := hX.pointwise_reduced_interpolation hn hK hN a π hg hp hC hc midpointTime
  have hb : ∀ᵐ γ ∂π, Real.exp (w γ)*(Real.exp (L 0 γ)+Real.exp (L 1 γ))/2 ≤
      Real.exp (L midpointTime γ) := by
    filter_upwards [hpw,hpow 0,hpow 1,hpow midpointTime] with γ hγ h0 h1 hm
    have hh : ENNReal.ofReal (Real.exp (w γ)/2)*
        ((r 0 γ)^(-(1/N))+(r 1 γ)^(-(1/N))) ≤ (r midpointTime γ)^(-(1/N)) := by
      calc
        _ = ENNReal.ofReal (Real.exp (w γ)/2)*(r 0 γ)^(-(1/N))+
            ENNReal.ofReal (Real.exp (w γ)/2)*(r 1 γ)^(-(1/N)) := mul_add _ _ _
        _ ≤ sigma K (N+1) (1/2) (dist (γ 0) (γ 1))*(r 0 γ)^(-(1/N))+
            sigma K (N+1) (1/2) (dist (γ 0) (γ 1))*(r 1 γ)^(-(1/N)) :=
          add_le_add (mul_le_mul' (hcoef _ dist_nonneg) le_rfl) (mul_le_mul' (hcoef _ dist_nonneg) le_rfl)
        _ ≤ _ := by simpa only [midpointTime,show (1:ℝ)-1/2=1/2 by norm_num] using hγ
    have hr := ENNReal.toReal_mono hm.2 hh
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_add h0.2 h1.2] at hr
    dsimp only [L]
    rw [Real.exp_log (ENNReal.toReal_pos h0.1 h0.2),
      Real.exp_log (ENNReal.toReal_pos h1.1 h1.2),Real.exp_log (ENNReal.toReal_pos hm.1 hm.2)]
    nlinarith only [hr]
  have hh := geometric_mean_sum π (hL 0).1 (hL 1).1 (hL midpointTime).1 hw hb
  have hiw : (∫ γ, w γ ∂π)=K*(wassersteinSq a.left a.right).toReal/(8*N) := by
    dsimp only [w]
    rw [integral_div,integral_const_mul,wassersteinSq_eq_cost hp,transportCost_plan_eq_integral π hi,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [hiw,(hL 0).2,(hL 1).2,(hL midpointTime).2,he.1,he.2] at hh
  exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
