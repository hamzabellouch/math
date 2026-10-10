import OAI.Geometry.RCD.Sobolev.ComposedGammaContinuity
import OAI.Geometry.RCD.Coordinates.RegularizedFisherInterpolation
import OAI.Geometry.RCD.Heat.HeatCutoffIntegral

namespace OAI

/-! # Initial-time continuity of the actual Fisher interpolation -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem regularizedFisherInterpolation_continuousAt
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    {T t ε : ℝ} (ht : t<T) (hε : 0<ε) :
    ContinuousAt (regularizedFisherInterpolation (hausdorff n X) hX.quadratic f w ε T) t := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let a := (T-t)/2
  have ha : 0<a := half_pos (sub_pos.mpr ht)
  have hat : a<T-t := by dsimp [a]; linarith
  let F := fun s => heatTail μ Q a ha f (T-s)
  have hF : Continuous F := (heatTail_continuous μ Q a ha f).comp (continuous_const.sub continuous_id)
  obtain ⟨L,hL⟩ := hX.heatTail_gradient_bound hn p f A hf ha
  have hval (s : ℝ) : ∀ᵐ x ∂μ, SobolevSpace.toLp μ Q (F s) x∈Icc 0 (A:ℝ) := by
    have hP := heatAt_nonneg μ Q a (heatAt μ Q (T-s-a) f)
      (heatAt_nonneg μ Q (T-s-a) f hf0)
    have hA := heatAt_abs_le_const μ Q a A (heatAt μ Q (T-s-a) f)
      (heatAt_abs_le_const μ Q (T-s-a) A f hf)
    filter_upwards [(Lp.coeFn_nonneg _).mpr hP,hA] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  obtain ⟨φ,b,db,C,D,J,B,E,_hφ,hb,_hdb,_hφ0,_hdφ,_hdb',hB,_hE,he⟩ :=
    shifted_logarithm_jets hε A.coe_nonneg
  have hc := composed_gamma_pairing_continuousAt μ Q (t:=t) hF.continuousAt
    (heatAt_continuous μ Q w).continuousAt L (fun s => hL (T-s)) hb B hB
  apply hc.congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, a<T-s :=
    (continuous_const.sub continuous_id).continuousAt.eventually (Ioi_mem_nhds hat)
  filter_upwards [hnear] with s hs
  have hpos : 0<T-s := ha.trans hs
  rw [regularizedFisherInterpolation,dite_eq_left hpos]
  have hv : (∫ x, heatAt μ Q s w x*b (SobolevSpace.toLp μ Q (F s) x)*
      localGamma μ Q (F s) (F s) x ∂μ) =
      ∫ x, heatAt μ Q s w x*localGamma μ Q (F s) (F s) x /
        (ε+SobolevSpace.toLp μ Q (F s) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hval s] with x hx
    rw [(he _ hx).2.1]
    ring
  rw [hv]
  dsimp only [F]
  rw [heatTail_eq μ Q a ha f (T-s) hs.le,heatSobolev_toLp]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
