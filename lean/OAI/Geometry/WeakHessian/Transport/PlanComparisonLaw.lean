import Mathlib
import OAI.Geometry.WeakHessian.Entropy.DensityCurve
import OAI.Geometry.WeakHessian.Transport.WeightedPlanComparison
import OAI.Geometry.WeakHessian.LocalBounds.OneSidedKernel
import OAI.Geometry.WeakHessian.LocalBounds.OneSidedBump

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_injective_nonneg {u v : Lp ℝ 2 m}
    (hu : ∀ᵐ x ∂m,0 ≤ u x) (hv : ∀ᵐ x ∂m,0 ≤ v x)
    (he : densityMeasure m u = densityMeasure m v) : u = v := by
  have H := (withDensity_eq_iff_of_sigmaFinite
    (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal.aemeasurable)
    (Lp.stronglyMeasurable v |>.measurable.ennreal_ofReal.aemeasurable)).mp he
  apply Lp.ext
  filter_upwards [H,hu,hv] with x hx hu hv
  have H := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv] using H

lemma WeakHessianUpperBound.rcd_weighted_plan_comparison_law {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u₀ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hu₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hlaw₀ : densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀ = π.map (fun γ => γ timeZero))
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {r D : ℝ} (hD : 0 ≤ D) (x₁ : X)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) x₁ ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D)
    {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X, ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      IsCoupling p (μ:Measure X)
        (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ∧
      FiniteEntropy m (μ:Measure X) ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧
      (∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r+δ*D) ∧
      QuadraticTransportCost p ≠ ∞ ∧ (QuadraticTransportCost p).toReal ≤
        2*((∫ s in (0:ℝ)..1,planKineticCost π/Real.exp (2*(K-a*CG)*T*(1-s))/2)+
          T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
             entropyReal (exponentialMeasure m (fun x => a*F x))
               (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsProbabilityMeasure π := hπ.1
  have hpν := hπ.of_measure_le_smul hmν
  obtain ⟨B',u,hu,hun,hub,hui,hum,hul,hunorm,_⟩ := hpν.exists_L2_density_curve hnfin hb
  have hB' (t : Time) : π.map (fun γ => γ t) ≤ (B' : ℝ≥0∞) • ν := by
    rw [← hul t]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      densityMeasure_le_const ((hub t).mono fun x hx => (le_abs_self _).trans hx)
  have hu0 : u timeZero = u₀ := densityMeasure_injective_nonneg (hun _) hu₀ ((hul _).trans hlaw₀.symm)
  obtain ⟨κ,hκ,hc,hn,hm,hsκ⟩ := exists_oneSidedKernel hδ
  have hi : Integrable κ := hc.continuous.integrable_of_hasCompactSupport hκ
  let := kernelMeasure_probability hi hn hm
  have hzκ : ∀ t,t < 0 → κ t = 0 := fun t ht => by
    by_contra hc
    exact (not_le_of_gt ht) (hsκ hc).1
  have hs0 : smoothDensity κ u 0 = u₀ :=
    (smoothDensity_zero_of_nonnegative_support hc.continuous hn hi hm hzκ u).trans hu0
  have hprop := fun s => hpν.smoothDensity_properties hB' hu hun hul hunorm hc.continuous hi hn hm s
  let := isProbabilityMeasure_timeAverageLaw π (kernelMeasure κ) 1
  let μ : ProbabilityMeasure X := ⟨timeAverageLaw π (kernelMeasure κ) 1,inferInstance⟩
  have hμ : (μ:Measure X) = densityMeasure ν (smoothDensity κ u 1) := (hprop 1).2.2.2.2.1.symm
  have hμB : (μ:Measure X) ≤ (B : ℝ≥0∞) • m := hπ.timeAverageLaw_le hB _ 1
  obtain ⟨b,R,hR,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hμE : FiniteEntropy m (μ:Measure X) :=
    finiteEntropy_of_bounded_supported hfin μ b ⟨R,hR.le⟩ (ae_iff.mp (hbR 1)) ENNReal.coe_ne_top hμB
  have h0support : ∀ᵐ x ∂ν,R+1 ≤ dist x b → u₀ x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    rw [hs0] at H
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨c,hc0,he,_,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h u₀ h0support
  have hu1V : Integrable (fun x => smoothDensity κ u 1 x*(c*dist x b)) ν := by
    convert (smoothDensity_integrable_dist hpν hb hB' hu hun hul hunorm hc.continuous hi hn hm 1 b).mul_const c using 1
    funext x; ring
  have hPm : ∫ x,cheegerHeat h T u₀ x ∂ν = 1 := by
    have H := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h u₀ hu₀
      (by simpa only [← hu0] using hui timeZero) hT).2
    rw [H,← hu0]; exact hum timeZero
  have hPn := cheegerHeat_nonneg h hT u₀ hu₀
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u₀) hPn (integrable_of_integral_eq_one hPm) hPm
  let μP : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u₀),inferInstance⟩
  have hEc := entropyReal_eq_reducedDensity (smoothDensity κ u 1) (hprop 1).1 (hprop 1).2.2.1
    (integrable_reducedEntropy (Lp.memLp _) (hprop 1).1 hu1V he) μ hμ
  have hEP := entropyReal_eq_reducedDensity (cheegerHeat h T u₀) hPn (integrable_of_integral_eq_one hPm)
    (integrable_reducedEntropy (Lp.memLp _) hPn (hPV T hT) he) μP rfl
  obtain ⟨p,hp,hp0,hp1,hpt,hcost⟩ := hHess.rcd_weighted_plan_comparison hN hrcd hfull hfin o
    hF hFb hGb hGc ha h hπ hb hgeo hB' hu hun hul hunorm hκ hc hn hm hT
  rw [hs0] at hp1 hcost
  refine ⟨μ,p,hp,⟨hp0.trans hμ.symm,hp1⟩,hμE,hμB,?_,hpt,?_⟩
  · exact timeAverageLaw_terminal_ball _ (kernelMeasure_ae_support hc.continuous hsκ) hD x₁ hgeo hs hl
  · change entropyReal ν (densityMeasure ν (cheegerHeat h T u₀)) = _ at hEP
    rw [hEc,hEP]
    convert hcost using 1; ring

end WeakHessian

end
end

end OAI
