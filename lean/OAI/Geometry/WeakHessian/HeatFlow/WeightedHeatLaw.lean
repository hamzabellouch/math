import Mathlib
import OAI.Geometry.WeakHessian.Transport.WeightedEntropyCoupling

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
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_densityMeasure_iff (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (f : X → ℝ) : Integrable f (densityMeasure m u) ↔ Integrable (fun x => u x*f x) m := by
  rw [densityMeasure,integrable_withDensity_iff_integrable_smul'
    (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hun] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]

lemma RCD.weighted_heat_law_finiteEntropy {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} (hVm : Measurable V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m V = 1)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      FiniteEntropy (exponentialMeasure m V) (μ:Measure X) ∧ FiniteEntropy m (μ:Measure X) ∧
      Integrable (fun x => dist x o) (μ:Measure X) ∧
      entropyReal (exponentialMeasure m V) (μ:Measure X) = entropyReal m (μ:Measure X)-∫ x,V x ∂(μ:Measure X) := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) (exponentialMeasure_comparable (m := m) hBV).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  obtain ⟨c,hc,he,_,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hin := integrable_of_integral_eq_one hum
  have hp := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun hin hT
  have hPn := cheegerHeat_nonneg h hT u hun
  have hPm := hp.2.trans hum
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u) hPn hp.1 hPm
  let μ : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u),inferInstance⟩
  have hE : FiniteEntropy ν (μ:Measure X) := densityMeasure_finiteEntropy _ hPn hp.1 (hPV T hT) he
  have hVi : Integrable V (μ:Measure X) := Integrable.of_bound hVm.aestronglyMeasurable BV
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hBV x)
  have hEm := (finiteEntropy_exponentialMeasure_iff hVm hVi).mp hE
  refine ⟨μ,rfl,hE,hEm,?_,entropyReal_exponentialMeasure hEm hVm hVi⟩
  have H := (integrable_densityMeasure_iff _ hPn _).mpr (hPV T hT)
  have H' := H.const_mul c⁻¹
  change Integrable (fun x => dist x o) (densityMeasure ν (cheegerHeat h T u))
  convert H' using 1
  funext x
  change dist x o = c⁻¹*(c*dist x o)
  rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

omit [SigmaFinite m] in
lemma RCD.weighted_heat_entropy_real_coupling {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m V = 1)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ B)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      p.map Prod.snd = densityMeasure (exponentialMeasure m V) u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤ ENNReal.ofReal
        (2*T*(entropyReal (exponentialMeasure m V) (densityMeasure (exponentialMeasure m V) u)-
          entropyReal (exponentialMeasure m V) (densityMeasure (exponentialMeasure m V) (cheegerHeat h T u)))) := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) (exponentialMeasure_comparable (m := m) hBV).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  obtain ⟨c,hc,he,huV,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hui := integrable_of_integral_eq_one hum
  have hp := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun hui hT
  have hPn := cheegerHeat_nonneg h hT u hun
  have hPm := hp.2.trans hum
  let := densityMeasure_probability_of_integrable u hun hui hum
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u) hPn hp.1 hPm
  let μ₀ : ProbabilityMeasure X := ⟨densityMeasure ν u,inferInstance⟩
  let μ₁ : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u),inferInstance⟩
  have h0 := entropyReal_eq_reducedDensity u hun hui
    (integrable_reducedEntropy (Lp.memLp _) hun huV he) μ₀ rfl
  have h1 := entropyReal_eq_reducedDensity (cheegerHeat h T u) hPn hp.1
    (integrable_reducedEntropy (Lp.memLp _) hPn (hPV T hT) he) μ₁ rfl
  obtain ⟨p,hp,hp0,hp1,hcost⟩ := hrcd.weighted_heat_entropy_coupling hN hfull hfin o hBV h u hun hum hB hub hR hT
  refine ⟨p,hp,hp0,hp1,?_⟩
  change entropyReal ν (densityMeasure ν u) = _ at h0
  change entropyReal ν (densityMeasure ν (cheegerHeat h T u)) = _ at h1
  rw [h0,h1,add_sub_add_right_eq_sub]
  exact hcost

end WeakHessian

end
end

end OAI
