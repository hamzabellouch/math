import Mathlib
import OAI.Geometry.WeakHessian.Transport.LocalizedPlanDual
import OAI.Geometry.WeakHessian.Transport.PlanComparisonLaw
import OAI.Geometry.WeakHessian.Entropy.ExplicitDensityNorm

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

lemma WeakHessianUpperBound.rcd_localized_plan_law {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u₀ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hu₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hlaw₀ : densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀ = π.map (fun γ => γ timeZero))
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {r D S : ℝ} (hD : 0 ≤ D) (x₁ : X)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) x₁ ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D)
    (htracks : ∀ᵐ γ ∂π,∀ t : Time,dist (γ t) o < S)
    {d β R T U c δ : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T < U) (hδ : 0 < δ)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
    ∃ μ : ProbabilityMeasure X, FiniteEntropy m (μ:Measure X) ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧
      (∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r+δ*D) ∧
      ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X))-
        (∫ x,boundedHopfMap f q x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ≤
      planKineticCost π/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip f q)
          (((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
          entropyReal (exponentialMeasure m (fun x => a*F x))
            (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hCF : 0 ≤ CF := (abs_nonneg (F o)).trans (hFb o)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVB
  rw [abs_of_pos ha] at hmν hνm
  let E : ℝ≥0 := (Real.exp (a*CF)).toNNReal
  have hE : (E:ℝ) = Real.exp (a*CF) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hnfin := hfin.of_le_smul (C := E) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsProbabilityMeasure π := hπ.1
  have hpν := hπ.of_measure_le_smul hmν
  have hB' (t : Time) : π.map (fun γ => γ t) ≤ ((B*E:ℝ≥0):ℝ≥0∞) • ν := by
    apply (hB t).trans
    simpa only [ENNReal.coe_mul,smul_smul,E,ν,ENNReal.ofReal] using smul_le_smul_left (B:ℝ≥0∞) hmν
  obtain ⟨u,hu,hun,_hub,hui,hum,hul,hunorm⟩ := hpν.exists_L2_density_curve_bound hnfin hb hB'
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
  obtain ⟨b,Rb,hRb,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hμE : FiniteEntropy m (μ:Measure X) :=
    finiteEntropy_of_bounded_supported hfin μ b ⟨Rb,hRb.le⟩ (ae_iff.mp (hbR 1)) ENNReal.coe_ne_top hμB
  have h0support : ∀ᵐ x ∂ν,Rb+1 ≤ dist x b → u₀ x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    rw [hs0] at H
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨cd,_hcd,he,_,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h u₀ h0support
  have hu1V : Integrable (fun x => smoothDensity κ u 1 x*(cd*dist x b)) ν := by
    convert (smoothDensity_integrable_dist hpν hb hB' hu hun hul hunorm hc.continuous hi hn hm 1 b).mul_const cd using 1
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
  have hdν := hdecay.of_measure_le_smul ENNReal.coe_ne_top hνm
  have hsup (s : ℝ) : ∀ᵐ x ∂ν,S ≤ dist x o → smoothDensity κ u s x = 0 := by
    have H := density_zero_of_ae_law (hprop s).1 (by
      rw [(hprop s).2.2.2.2.1]
      exact timeAverageLaw_ae_of_tracks (kernelMeasure κ) (measurableSet_lt (show Measurable (fun x : X => dist x o) from by fun_prop) measurable_const) htracks s)
    filter_upwards [H] with x hx hs
    exact hx (not_lt.mpr hs)
  have hQ (s : ℝ) : ‖smoothDensity κ u s‖*‖hdν.toLp (fun x => Real.exp (-d*dist x o))‖ ≤
      ((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF) := by
    have H := norm_product_of_compression (B := B) (E := E) (by rw [hE]; exact Real.one_le_exp (by positivity)) hνm
      ((hprop s).2.2.2.2.2) hdecay hdν
    rw [hE,← Real.exp_nat_mul] at H
    convert H using 1; first | rfl | (congr 1; ring_nf)
  refine ⟨μ,hμE,hμB,timeAverageLaw_terminal_ball _ (kernelMeasure_ae_support hc.continuous hsκ) hD x₁ hgeo hs hl,?_⟩
  intro f hf q hq
  have HD := hHess.rcd_localized_plan_dual hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hπ hb hgeo hB' hu hun hul hunorm hκ hc hn hm hd hdβ hdν hsup hlocal hT hTU hQ hsmall f hf hq
  rw [hs0] at HD
  change entropyReal ν (densityMeasure ν (cheegerHeat h T u₀)) = _ at hEP
  rw [hEc,hEP]
  rw [hμ,integral_densityMeasure ν _ (hprop 1).1,integral_densityMeasure ν _ hPn]
  linarith only [HD]
end WeakHessian

end
end

end OAI
