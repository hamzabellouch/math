import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatLaplacianIntegral

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {m : Measure X}
lemma cheeger_scaled_resolvent_nonneg (h : QuadraticCheegerEnergy m)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) :
    ∀ᵐ x ∂m,0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u x := by
  let η : ℝ → ℝ := fun r => max r 0
  have hη : LipschitzWith 1 η := lipschitzWith_posPart
  have hη0 : η 0 = 0 := max_self _
  have hufix : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u,hu] with x hx hu
    simpa only [Function.comp_apply,η,max_eq_left hu] using hx
  have hQη (f : Lp ℝ 2 m) :
      cheegerEnergy m (hη.compLp hη0 f : X → ℝ) ≤ cheegerEnergy m (f : X → ℝ) := by
    rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
    exact cheegerEnergy_normalContraction hη hη0 f
  have hfix := ((cheeger_closedQuadraticEnergy h).scale ht).resolvent_normal_fixed m hη hη0
    (fun f => by gcongr; exact hQη f) u hufix
  filter_upwards [hη.coeFn_compLp hη0 (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u)] with x hx
  rw [hfix] at hx
  change ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x =
    max (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x) 0 at hx
  change 0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x
  rw [hx]
  exact le_max_right _ _

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma scaled_generator_weighted {u v : Lp ℝ 2 m} {V : X → ℝ} {t : ℝ}
    (hu : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hv : MemLp (fun x => v x*Real.exp (V x)) 2 m) :
    MemLp (fun x => (t⁻¹ • (v-u)) x*Real.exp (V x)) 2 m := by
  have H := (hv.sub hu).const_smul (t⁻¹)
  apply MemLp.ae_eq _ H
  filter_upwards [Lp.coeFn_smul (t⁻¹) (v-u),Lp.coeFn_sub v u] with x hs hd
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hd]
  simp only [Pi.sub_apply]
  ring

lemma CurvatureDimension.cheegerResolvent_mass_localized {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    (∫ x,((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u x ∂m) = ∫ x,u x ∂m := by
  let Q := cheeger_closedQuadraticEnergy h
  let v := (Q.scale ht).resolventLinear u
  let A := t⁻¹ • (v-u)
  have huv : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht u v).mp rfl
  have hW : MemLp (fun x => v x*Real.exp (V x)) 2 m :=
    hcd.cheegerResolvent_weighted hfin o h u ht hV hU hsmall
  have hAW : MemLp (fun x => A x*Real.exp (V x)) 2 m := scaled_generator_weighted hU hW
  have hAz := hcd.cheegerHeat_laplacian_integral_zero hfin o h huv hV hW hAW hdecay (t := 0) le_rfl
  simp only [cheegerHeat_zero,one_apply_eq_self] at hAz
  have hAi : (∫ x,A x ∂m) = t⁻¹*((∫ x,v x ∂m)-(∫ x,u x ∂m)) := by
    calc
      _ = ∫ x,t⁻¹*(v x-u x) ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (t⁻¹) (v-u),Lp.coeFn_sub v u] with x hs hd
        dsimp only [A]
        rw [hs]
        simp only [Pi.smul_apply,smul_eq_mul]
        rw [hd]
        rfl
      _ = _ := by rw [integral_const_mul,integral_sub (integrable_of_memLp_mul_exp hW hdecay)
        (integrable_of_memLp_mul_exp hU hdecay)]
  rw [hAz] at hAi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hAi.symm).resolve_left (inv_ne_zero ht.ne'))
end WeakHessian

end
end InlinedFile0

end OAI
