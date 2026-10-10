import Mathlib
import OAI.Geometry.WeakHessian.Transport.LocalizedPlanLaw
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatConcentration
import OAI.Geometry.WeakHessian.Geodesics.MidpointDualTests
import OAI.Geometry.WeakHessian.Entropy.EntropyDrop
import OAI.Geometry.WeakHessian.LocalBounds.WeightedInitialLaw
import OAI.Geometry.WeakHessian.LocalBounds.LocalizedScaling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_common_local_heat_legs {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (o x₀ x₁ : X) (μ₀ : ProbabilityMeasure X) {r : ℝ} (hr : 0 ≤ r)
    (hsμ : ∀ᵐ x ∂(μ₀:Measure X),dist x o ≤ r)
    {B : ℝ≥0} (hB : 0 < B) (hcap : (μ₀:Measure X) ≤ (B:ℝ≥0∞) • m)
    {d : ℝ} (hd : 0 < d) (he : Integrable (fun x => Real.exp (-(d*dist x o))) m)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
    {π₀ π₁ : Measure (Curve X)} {C₀ C₁ : ℝ≥0} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hπ₀ : IsTestPlan m π₀) (hπ₁ : IsTestPlan m π₁)
    (hb₀ : BoundedTracks π₀) (hb₁ : BoundedTracks π₁)
    (hg₀ : ∀ᵐ γ ∂π₀,IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂π₁,IsGeodesic γ)
    (hi₀ : π₀.map (fun γ => γ timeZero) = (μ₀:Measure X))
    (hi₁ : π₁.map (fun γ => γ timeZero) = (μ₀:Measure X))
    (hcap₀ : ∀ t : Time,π₀.map (fun γ => γ t) ≤ (C₀:ℝ≥0∞) • m)
    (hcap₁ : ∀ t : Time,π₁.map (fun γ => γ t) ≤ (C₁:ℝ≥0∞) • m)
    {D₀ D₁ S R c : ℝ} (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁)
    (hs₀ : ∀ᵐ γ ∂π₀,dist (γ timeOne) x₀ ≤ r)
    (hs₁ : ∀ᵐ γ ∂π₁,dist (γ timeOne) x₁ ≤ r)
    (hl₀ : ∀ᵐ γ ∂π₀,dist (γ timeZero) (γ timeOne) ≤ D₀)
    (hl₁ : ∀ᵐ γ ∂π₁,dist (γ timeZero) (γ timeOne) ≤ D₁)
    (hE₀ : planKineticCost π₀ ≤ D₀^2) (hE₁ : planKineticCost π₁ ≤ D₁^2)
    (htracks₀ : ∀ᵐ γ ∂π₀,∀ t : Time,dist (γ t) o < S)
    (htracks₁ : ∀ᵐ γ ∂π₁,∀ t : Time,dist (γ t) o < S)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    {Rd : ℝ} (hRd : dist x₀ x₁ ≤ Rd) {LD₀ LD₁ : ℝ≥0}
    (hLD₀ : LipschitzWith LD₀ (boundedHopfMap (midpointDualTest x₀ Rd) 1))
    (hLD₁ : LipschitzWith LD₁ (boundedHopfMap (midpointDualTest x₁ Rd) 1))
    {a T U δ β q : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (hTU : T < U)
    (hδ : 0 < δ) (hq : 0 < q) (hdβ : d ≤ β)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
    ∃ M : ℝ,0 ≤ M ∧
      M^2 ≤ 4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(d*dist x o)) ∂m)+1)+
        16*(T*a)*CF+16*T^2*d^2 ∧
      dist x₀ x₁^2/4-(LD₀:ℝ)*(r+δ*D₀)-(LD₁:ℝ)*(r+δ*D₁)-
        2*(‖midpointDualTest x₀ Rd‖+‖midpointDualTest x₁ Rd‖)*q ≤
        (D₀^2+D₁^2)/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip (midpointDualTest x₀ Rd) q)
          (((C₀:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        curvatureTailBound K a c CG U (hopfUniformLip (midpointDualTest x₁ Rd) q)
          (((C₁:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        T*(|Real.log (C₀:ℝ)|+|Real.log (C₁:ℝ)|+
          2*((∫ x,Real.exp (-(d*dist x o)) ∂m)+1)+2*d*M)+
        (a*T)*(2*F o-F x₀-F x₁+(L:ℝ)*(2*M+2*r+δ*(D₀+D₁))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  let h := hrcd.weighted_quadraticCheegerEnergy hfin o hVB
  obtain ⟨Bu,u,hun,hub,hum,hul⟩ := exists_weighted_initial_density hfin o hVB μ₀ hcap
  obtain ⟨μ,hμ,hμE,hμi,hM⟩ := hrcd.weighted_heat_concentration hN hfull hfin o hF.continuous hFb
    ha.le h u hun hum Bu.property hub hr (by rwa [hul]) hB (by rwa [hul]) hd he hT
  obtain ⟨η₀,hη₀E,hη₀cap,hη₀s,hcost₀⟩ := hHess.rcd_localized_plan_law hN hrcd hfull hfin o hF hFb hGb hGc
    ha h u hun hπ₀ hb₀ hg₀ (hul.trans hi₀.symm) hcap₀ hD₀ x₀ hs₀ hl₀ htracks₀
    hd.le hdβ hdecay hlocal hT hTU hδ hsmall
  obtain ⟨η₁,hη₁E,hη₁cap,hη₁s,hcost₁⟩ := hHess.rcd_localized_plan_law hN hrcd hfull hfin o hF hFb hGb hGc
    ha h u hun hπ₁ hb₁ hg₁ (hul.trans hi₁.symm) hcap₁ hD₁ x₁ hs₁ hl₁ htracks₁
    hd.le hdβ hdecay hlocal hT hTU hδ hsmall
  have hRn : 0 ≤ Rd := dist_nonneg.trans hRd
  specialize hcost₀ (midpointDualTest x₀ Rd) (midpointDualTest_compact x₀ hRn) q hq
  specialize hcost₁ (midpointDualTest x₁ Rd) (midpointDualTest_compact x₁ hRn) q hq
  rw [← hμ] at hcost₀ hcost₁
  have Hlow := midpoint_dual_lower x₀ x₁ hRd η₀ η₁ μ hLD₀ hLD₁ hη₀s hη₁s hq
  have H₀ := entropy_exponential_drop_bound hF hFb ha.le hd.le o x₀ η₀ μ hη₀E hμE hμi he hC₀ hη₀cap hη₀s
  have H₁ := entropy_exponential_drop_bound hF hFb ha.le hd.le o x₁ η₁ μ hη₁E hμE hμi he hC₁ hη₁cap hη₁s
  have Hdrop₀ := mul_le_mul_of_nonneg_left H₀ hT
  have Hdrop₁ := mul_le_mul_of_nonneg_left H₁ hT
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hA := localizedActionBound_nonneg (K := K) (c := c) ha.le hCG hT
  have HA₀ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE₀ (by norm_num : (0:ℝ) ≤ 2)) hA
  have HA₁ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE₁ (by norm_num : (0:ℝ) ≤ 2)) hA
  refine ⟨∫ x,dist x o ∂(μ:Measure X),integral_nonneg fun x => dist_nonneg,hM,?_⟩
  nlinarith only [Hlow,hcost₀,hcost₁,Hdrop₀,Hdrop₁,HA₀,HA₁]
end WeakHessian

end
end

end OAI
