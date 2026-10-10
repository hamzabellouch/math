import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TargetEVI

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile69
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma densityMeasure_le_const {u : Lp ℝ 2 m} {B : ℝ} (hu : ∀ᵐ x ∂m,u x ≤ B) :
    densityMeasure m u ≤ ENNReal.ofReal B • m := by
  rw [densityMeasure,← withDensity_const]
  exact withDensity_mono (hu.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

lemma RCD.cheegerHeat_comparison_shift {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ (a+b):Measure X) (ν c:Measure X)-
      quadraticWassersteinSq (μ a:Measure X) (ν c:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν c:Measure X)-entropyReal m (μ (a+t):Measure X)) := by
  have hui := integrable_of_integral_eq_one hum
  have hvi := integrable_of_integral_eq_one hvm
  have hua := cheegerHeat_nonneg h ha u hun
  have hvc := cheegerHeat_nonneg h hc v hvn
  have hvcI := (cheegerHeat_integrable hfin o h v hvi hc).1
  have hUa := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ha).1
  have hUc := (hrcd.1.cheegerHeat_weighted hfin o h v hV hU' hc).1
  have hum' : ∫ x,cheegerHeat h a u x ∂m = 1 :=
    (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hui ha).2.trans hum
  have hμ' (t : ℝ) (ht : 0 ≤ t) :
      (μ (a+t):Measure X) = densityMeasure m (cheegerHeat h t (cheegerHeat h a u)) := by
    rw [hμ _ (add_nonneg ha ht),add_comm a t,cheegerHeat_add h ht ha]
    rfl
  let : IsProbabilityMeasure (densityMeasure m (cheegerHeat h c v)) := hν c hc ▸ inferInstance
  have hνE : FiniteEntropy m (ν c:Measure X) := by
    rw [hν c hc]
    exact densityMeasure_finiteEntropy _ hvc hvcI (weighted_pairing hUc hD).1 hdecayi
  have hνM : Integrable (fun x => dist x o^2) (ν c:Measure X) := by
    rw [hν c hc]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _ hvc hUc (hW 0).1
  have hdν : (ν c:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hν c hc]
    exact densityMeasure_le_const ((cheegerHeat_bounded h hc hC v hvC).mono fun _ hx => (le_abs_self _).trans hx)
  have H := hrcd.cheegerHeat_comparison_weighted_target hN hfull hfin o h (cheegerHeat h a u)
    hua hum' hB (cheegerHeat_bounded h ha hB u huB) hV hUa hdecay hD hdecayi hhalf hhalfi hW
    (fun t => μ (a+t)) hμ' (ν c) (fun x => Real.sqrt (cheegerHeat h c v x))
    (densityMeasure_sqrt_memLp _ hvc hvcI) (Lp.stronglyMeasurable _ |>.measurable.sqrt)
    ((hν c hc).trans (densityMeasure_eq_square_sqrt _ hvc)) hνE hνM ENNReal.ofReal_ne_top hdν hb
  simpa only [add_zero] using H
end WeakHessian

end
end InlinedFile69

end OAI
