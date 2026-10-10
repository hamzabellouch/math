import Mathlib
import OAI.Geometry.WeakHessian.Transport.WeightedEntropyCoupling
import OAI.Geometry.WeakHessian.Transport.PlanEntropyCoupling
import OAI.Geometry.WeakHessian.Transport.SmoothedPlanSupport

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_plan_comparison {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤
      (B : ℝ≥0∞) • exponentialMeasure m (fun x => a*F x))
    {u : Time → Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hu : StronglyMeasurable u)
    (hun : ∀ t,∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u t x)
    (hlaw : ∀ t,densityMeasure (exponentialMeasure m (fun x => a*F x)) (u t) =
      π.map (fun γ => γ t)) (hnorm : ∀ t,‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r,0 ≤ κ r) (hm : ∫ r,κ r = 1) {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure (exponentialMeasure m (fun x => a*F x)) (smoothDensity κ u 1) ∧
      p.map Prod.snd = densityMeasure (exponentialMeasure m (fun x => a*F x))
        (cheegerHeat h T (smoothDensity κ u 0)) ∧
      QuadraticTransportCost p ≠ ∞ ∧ (QuadraticTransportCost p).toReal ≤
        2*((∫ s in (0:ℝ)..1,planKineticCost π/Real.exp (2*(K-a*CG)*T*(1-s))/2)+
          T*((∫ x,reducedEntropy (smoothDensity κ u 1 x) ∂exponentialMeasure m (fun x => a*F x))-
             (∫ x,reducedEntropy (cheegerHeat h T (smoothDensity κ u 0) x)
                ∂exponentialMeasure m (fun x => a*F x)))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsProbabilityMeasure π := hπ.1
  have hpν := hπ.of_measure_le_smul hmν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure hmν hνm
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hi : Integrable κ := hc.continuous.integrable_of_hasCompactSupport hκ
  have hprop := fun s => hpν.smoothDensity_properties hB hu hun hlaw hnorm hc.continuous hi hn hm s
  let := kernelMeasure_probability hi hn hm
  obtain ⟨b,R,hR,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hsupport : ∀ᵐ x ∂ν,R+1 ≤ dist x b → smoothDensity κ u 0 x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨c,hc0,hV,hUV,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h
    (smoothDensity κ u 0) hsupport
  have hu1V := (smoothDensity_integrable_dist hpν hb hB hu hun hlaw hnorm hc.continuous hi hn hm 1 b).mul_const c
  have hu1V' : Integrable (fun x => smoothDensity κ u 1 x*(c*dist x b)) ν := by
    convert hu1V using 1
    funext x; ring
  have hPm := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h (smoothDensity κ u 0)
    (hprop 0).1 (hprop 0).2.2.1 hT).2.trans (hprop 0).2.2.2.1
  apply cheegerHeat_plan_entropy_coupling hnfin o hID hnpar h (k := K-a*CG) ?_
    hpν hb hgeo hB hu hun hlaw hnorm hκ hc hn hm hT hPm hu1V' (hPV T hT) hV
  intro f ξ hf hξ0 Cξ hCξ hξb t ht
  have H := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o
    hF hFb hGb hGc ha h hf hCξ hξb hξ0 ht
  have hi1 : (∫ x,ξ x*gamma ν (cheegerHeat h t f) (cheegerHeat h t f) x ∂ν) =
      ∫ x,ξ x*(weakGradient ν (cheegerHeat h t f) x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) (cheegerHeat h t f)] with x hx
    rw [hx]
  have hi2 : (∫ x,cheegerHeat h t ξ x*gamma ν f f x ∂ν) =
      ∫ x,cheegerHeat h t ξ x*(weakGradient ν f x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) (f : X → ℝ)] with x hx
    rw [hx]
  change (∫ x,ξ x*gamma ν (cheegerHeat h t f) (cheegerHeat h t f) x ∂ν) ≤
    Real.exp (-(2*(K-a*CG))*t)*(∫ x,cheegerHeat h t ξ x*gamma ν f f x ∂ν) at H
  rw [hi1,hi2] at H
  have H' := mul_le_mul_of_nonneg_left H (Real.exp_pos (2*(K-a*CG)*t)).le
  have he : Real.exp (2*(K-a*CG)*t)*Real.exp (-(2*(K-a*CG))*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring_nf
  simpa only [← mul_assoc,he,one_mul] using H'

end WeakHessian

end
end

end OAI
