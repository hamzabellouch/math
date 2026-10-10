import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatLaplacianIntegral
import OAI.Geometry.WeakHessian.Measure.DecayCutoffLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_mass_of_weighted_resolvents {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n, 0 < ts n)
    (hsmall : ∀ n, ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    hcd.cheegerResolvent_weighted hfinite o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (hcd.cheegerResolvent_weighted_norm hfinite o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := by
    have H := ((hW n).sub hU).const_smul ((ts n)⁻¹)
    apply MemLp.ae_eq _ H
    filter_upwards [Lp.coeFn_smul ((ts n)⁻¹) (us n-u),Lp.coeFn_sub (us n) u] with x hs hd
    dsimp only [As]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    ring
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have H1 := integral_tendsto_of_weighted_bound hdecay hfinite o hum hU hW hWnorm
  have hWt (n : ℕ) := (hcd.cheegerHeat_weighted hfinite o h (us n) hV (hW n) ht).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h t (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*t) := by
    exact (hcd.cheegerHeat_weighted_norm hfinite o h (us n) hV (hW n) ht).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have H2 := integral_tendsto_of_weighted_bound hdecay hfinite o
    ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hum)
    (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1 hWt hWtnorm
  have he (n : ℕ) : (∫ x,cheegerHeat h t (us n) x ∂m) = ∫ x,us n x ∂m :=
    hcd.cheegerHeat_mass_weighted_generator hfinite o h (hus n) hV (hW n) (hAw n) hdecay ht
  simp_rw [Function.comp_def,he] at H2
  exact tendsto_nhds_unique H2 H1

lemma CurvatureDimension.cheegerHeat_mass_localized {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact hcd.cheegerHeat_mass_of_weighted_resolvents hfinite o h u hV hU hdecay hpos hsmall hlim ht
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
