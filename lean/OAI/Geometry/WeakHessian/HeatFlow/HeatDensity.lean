import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.RealHeatRangeError
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}
  [IsProbabilityMeasure m]

def heatDensity (h : QuadraticCheegerEnergy m) (ε : ℝ) (u : Lp ℝ 2 m) (t : ℝ) : Lp ℝ 2 m :=
  constLp 1 + ε • cheegerHeat h t u

lemma heatDensity_coe (h : QuadraticCheegerEnergy m) (ε : ℝ) (u : Lp ℝ 2 m) (t : ℝ) :
    (heatDensity h ε u t : X → ℝ) =ᵐ[m] (fun x => 1+ε*(cheegerHeat h t u x)) := by
  filter_upwards [Lp.coeFn_add (constLp (m := m) 1) (ε • cheegerHeat h t u),
    constLp_coe (m := m) 1, Lp.coeFn_smul ε (cheegerHeat h t u)] with x ha hc hs
  simp only [heatDensity, ha, Pi.add_apply, hc, hs, Pi.smul_apply, smul_eq_mul]

lemma heatDensity_mass (h : QuadraticCheegerEnergy m) (ε : ℝ) (u : Lp ℝ 2 m)
    (hu : ∫ x, u x ∂m = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, heatDensity h ε u t x ∂m) = 1 := by
  rw [integral_congr_ae (heatDensity_coe h ε u t),
    integral_add (integrable_const _) ((MemLp.integrable (by norm_num) (Lp.memLp _)).const_mul ε),
    integral_const_mul, cheegerHeat_mass h ht u, hu]
  simp

lemma heatDensity_bounds (h : QuadraticCheegerEnergy m) {ε B t : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (ht : 0 ≤ t) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, heatDensity h ε u t x ∈ Icc (1-ε*B) (1+ε*B) := by
  filter_upwards [heatDensity_coe h ε u t, cheegerHeat_bounded h ht hB u hu] with x hx hb
  rw [hx]
  rcases abs_le.mp hb with ⟨hb0,hb1⟩
  constructor <;> nlinarith

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma heatDensity_continuousOn (h : QuadraticCheegerEnergy m) (ε : ℝ)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) :
    ContinuousOn (heatDensity h ε u) (Ici 0) := by
  have hc := ((cheeger_closedQuadraticEnergy h).heat_lipschitz_on_generator m hu).continuousOn
  change ContinuousOn (fun t => cheegerHeat h t u) (Ici 0) at hc
  exact continuousOn_const.add (hc.const_smul ε)

lemma heatDensity_affine_deriv (h : QuadraticCheegerEnergy m) (ε : ℝ)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {s d r : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun v => heatDensity h ε u (s+d*v))
      ((ε*d) • cheegerHeat h (s+d*r) A) (Ici r) r := by
  have hg := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu
    (show 0 ≤ s+d*r by positivity)
  have ha : HasDerivWithinAt (fun v : ℝ => s+d*v) d (Ici r) r := by
    simpa only [mul_one, id_eq] using! (((hasDerivWithinAt_id r (Ici r)).const_mul d).const_add s)
  have H := hg.scomp_of_eq (h := fun v : ℝ => s+d*v) r ha
    (show MapsTo (fun v : ℝ => s+d*v) (Ici r) (Ici (s+d*r)) from
      by intro v hv; exact add_le_add_right (mul_le_mul_of_nonneg_left hv hd) s) rfl
  have H' := (H.const_smul ε).const_add (constLp (m := m) 1)
  simpa only [Function.comp_def, Pi.smul_apply, heatDensity, cheegerHeat, smul_smul] using! H'

end WeakHessian

open Set Filter
open scoped Topology ENNReal NNReal

end
end InlinedFile0

end OAI
