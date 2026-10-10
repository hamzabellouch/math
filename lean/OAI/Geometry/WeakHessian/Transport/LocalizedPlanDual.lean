import Mathlib
import OAI.Geometry.WeakHessian.Measure.CurvatureTail
import OAI.Geometry.WeakHessian.Transport.PerturbedPlanDual
import OAI.Geometry.WeakHessian.LocalBounds.LocalOffset
import OAI.Geometry.WeakHessian.Transport.LocalizedActionBound
import OAI.Geometry.WeakHessian.Transport.WeightedEntropyCoupling
import OAI.Geometry.WeakHessian.Transport.SmoothedPlanSupport

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_localized_plan_dual {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
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
    (hn : ∀ r,0 ≤ κ r) (hm : ∫ r,κ r = 1)
    {d β r R T U Q c : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 (exponentialMeasure m (fun x => a*F x)))
    (hsupp : ∀ s : ℝ,∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),r ≤ dist x o → smoothDensity κ u s x = 0)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T < U)
    (hQ : ∀ s : ℝ,‖smoothDensity κ u s‖*‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖ ≤ Q)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    let ν := exponentialMeasure m (fun x => a*F x)
    (∫ x,smoothDensity κ u 1 x*boundedHopfMap f (q+1) x ∂ν)-
      (∫ x,cheegerHeat h T (smoothDensity κ u 0) x*boundedHopfMap f q x ∂ν)+
      T*((∫ x,reducedEntropy (cheegerHeat h T (smoothDensity κ u 0) x) ∂ν)-
        (∫ x,reducedEntropy (smoothDensity κ u 1 x) ∂ν)) ≤
      planKineticCost π/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip f q) Q d β R r := by
  dsimp only
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
  obtain ⟨b,Rb,hRb,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hsupport : ∀ᵐ x ∂ν,Rb+1 ≤ dist x b → smoothDensity κ u 0 x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨cd,hcd,hV,hUV,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h
    (smoothDensity κ u 0) hsupport
  have hu1V : Integrable (fun x => smoothDensity κ u 1 x*(cd*dist x b)) ν := by
    convert (smoothDensity_integrable_dist hpν hb hB hu hun hlaw hnorm hc.continuous hi hn hm 1 b).mul_const cd using 1
    funext x; ring
  have hPm := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h (smoothDensity κ u 0)
    (hprop 0).1 (hprop 0).2.2.1 hT).2.trans (hprop 0).2.2.2.1
  have hPn := cheegerHeat_nonneg h hT (smoothDensity κ u 0) (hprop 0).1
  apply entropy_dual_of_regularized (cheegerHeat h T (smoothDensity κ u 0)) (smoothDensity κ u 1)
    (integrable_of_integral_eq_one hPm) (hprop 1).2.2.1 (hPm.trans (hprop 1).2.2.2.1.symm)
    hPn (hprop 1).1 (hPV T hT) hu1V hV (D := compactHopfDualBound hnfin o f hf hq/2)
  intro ε hε
  let Eerror := curvatureTailBound K a c CG U (hopfUniformLip f q) Q d β R r
  let A := fun δ : ℝ => planKineticCost π/2*(1-2*(K-a*c)*δ-(K-a*c)*T+
    2*|K-a*c| *(δ+T)*(localizedHeatM K a CG (δ+T)-1)+4*(K-a*c)^2*(δ+T)^2)+Eerror+
      ε*compactHopfDualBound hnfin o f hf hq/2
  have hAc : ContinuousAt A 0 := by dsimp [A,localizedHeatM]; fun_prop
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have H := compact_dual_heat_offset_limit_local hnfin h (smoothDensity κ u 0) (smoothDensity κ u 1)
    (boundedHopfMap_memLp_compact hnfin f o hf hq)
    (boundedHopfMap_memLp_compact hnfin f o hf (by linarith : 0 < q+1)) hT hε
    (sub_pos.mpr hTU) hAc (by
      intro δ hδ
      have hθU (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : backwardsHeatTime δ T s ≤ U := by
        dsimp [backwardsHeatTime]
        rw [max_eq_left (by linarith [hs.2])]
        nlinarith [hδ.2,hs.1]
      have hθn (s : ℝ) : 0 ≤ backwardsHeatTime δ T s := (backwardsHeatTime_pos hδ.1 hT s).le
      have hcert := fun s => hHess.localized_heat_certificate hN hrcd hfull hfin o hF hFb hGb hGc ha h
        B.coe_nonneg (hprop s).2.1 (hprop s).1 c (hθn s)
      have HD := cheegerHeat_plan_entropy_dual_error hnfin o hID hnpar h hpν hb hgeo hB hu hun hlaw hnorm
        hκ hc hn hm hδ.1 hT hq f hf (localizedHeatFactor_continuousOn K a c CG)
        (fun t ht => localizedHeatFactor_pos K a c CG ht)
        (R := fun s => localizedHeatError h (smoothDensity κ u s) G K a c CG (backwardsHeatTime δ T s))
        (fun s _ => (hcert s).1) (fun s _ => (hcert s).2.1) (by
          intro s hs v hv
          have HB := (hcert s).2.2 v hv
          have hEn : 0 ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient ν v x)^2 ∂ν := by
            apply integral_nonneg_of_ae
            filter_upwards [cheegerHeat_nonneg h (hθn s) _ (hprop s).1] with x hx
            positivity
          have hMt : localizedHeatM K a CG (backwardsHeatTime δ T s) ≤ localizedHeatM K a CG U := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (hθU s hs) (by positivity)
          have hscale : 4*a*(CG+|c|)*(backwardsHeatTime δ T s)*localizedHeatM K a CG (backwardsHeatTime δ T s) ≤ 1 := by
            apply le_trans _ hsmall
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hθU s hs) (by positivity)) hMt
              (Real.exp_pos _).le (mul_nonneg (by positivity) (hT.trans hTU.le))
          have Hscale := mul_le_mul_of_nonneg_right hscale hEn
          nlinarith only [HB.2,Hscale]) (by
          intro s hs v hv hDb
          exact hHess.localized_heatError_tail_bound hN hrcd hfull hfin o hF hFb hGb hGc ha h
            hv (hopfUniformLip_nonneg f hq) hDb (hprop s).2.2.1 B.coe_nonneg (hprop s).2.1 (hprop s).1
            hd hdβ hdecay (hsupp s) hlocal (hθn s) (hθU s hs) (hQ s)) ε hε
      have HA := localized_action_integral_bound (K := K) (c := c) ha.le hCG hδ.1.le hT (planKineticCost_nonneg π)
      exact HD.trans (by change _ ≤ A δ; dsimp only [A,Eerror]; linarith))
  simpa only [A,Eerror,localizedActionBound,mul_zero,sub_zero,zero_add,mul_div_assoc] using H

end WeakHessian

end
end

end OAI
