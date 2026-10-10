import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatVariance

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile213
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_reverse_poincare_test {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    (2*(∫ s in (0:ℝ)..T,Real.exp (2*(K-a*CG)*s)))*
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
        (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,(f x)^2*cheegerHeat h T ξ x ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,(cheegerHeat h T f x)^2*ξ x ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCξ ξ hξb)
  have hvs0 (n : ℕ) : ∀ᵐ x ∂ν,0 ≤ vs n x := by
    rw [he n]; exact cheeger_double_resolvent_nonneg h (hts n) ξ hξ0
  have hvs : Tendsto vs atTop (𝓝 ξ) := by
    have H := cheeger_double_resolvent_tendsto h hts ht0 ξ
    exact H.congr (fun n => (he n).symm)
  have hΓ : MemLp (gamma ν (cheegerHeat h T f) (cheegerHeat h T f)) 2 ν :=
    hrcd.weighted_heat_gamma_memLp hN hfull hfin o hV hVB h hf hCf hCAf hfb hAfb hT
  have hsq (u : Lp ℝ 2 ν) {B : ℝ} (hb : ∀ᵐ x ∂ν,|u x| ≤ B) : MemLp (fun x => (u x)^2) 2 ν := by
    simpa only [pow_two] using memLp_mul_bounded (Lp.memLp u) (Lp.aestronglyMeasurable u) hb
  have hsq0 := hsq f hfb
  have hsqT := hsq (cheegerHeat h T f) (cheegerHeat_bounded h hT hCf f hfb)
  have hid (v : Lp ℝ 2 ν) {q : X → ℝ} (hq : MemLp q 2 ν) :
      (∫ x,v x*q x ∂ν) = ⟪hq.toLp q,v⟫_ℝ := by
    simpa only [Lp.toLp_coeFn] using integral_mul_eq_inner (Lp.memLp v) hq
  have hid' (v : Lp ℝ 2 ν) {q : X → ℝ} (hq : MemLp q 2 ν) :
      (∫ x,q x*v x ∂ν) = ⟪hq.toLp q,v⟫_ℝ := by
    simpa only [mul_comm] using hid v hq
  have hleft : Tendsto (fun n => ∫ x,vs n x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)
      atTop (𝓝 (∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)) := by
    simp only [hid _ hΓ]
    exact (tendsto_const_nhds (x := hΓ.toLp _)).inner hvs
  have hheat := (cheegerHeat h T).continuous.tendsto ξ |>.comp hvs
  have hright : Tendsto (fun n => ∫ x,(f x)^2*cheegerHeat h T (vs n) x ∂ν)
      atTop (𝓝 (∫ x,(f x)^2*cheegerHeat h T ξ x ∂ν)) := by
    simp only [hid' _ hsq0]
    simpa only [Function.comp_def] using (tendsto_const_nhds (x := hsq0.toLp _)).inner hheat
  have hright' : Tendsto (fun n => ∫ x,(cheegerHeat h T f x)^2*vs n x ∂ν)
      atTop (𝓝 (∫ x,(cheegerHeat h T f x)^2*ξ x ∂ν)) := by
    simp only [hid' _ hsqT]
    exact (tendsto_const_nhds (x := hsqT.toLp _)).inner hvs
  apply le_of_tendsto_of_tendsto (hleft.const_mul _) (hright.sub hright') (Eventually.of_forall fun n => ?_)
  exact hHess.rcd_weighted_reverse_poincare_core hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hf (hg n) hCf hCAf hCξ hfb hAfb (hvb n) (hvs0 n) hT

lemma weighted_reverse_coefficient_lower (k : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    2*T*Real.exp (-2*|k| *T) ≤ 2*(∫ s in (0:ℝ)..T,Real.exp (2*k*s)) := by
  have hc : IntervalIntegrable (fun s => Real.exp (2*k*s)) volume 0 T :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have H := intervalIntegral.integral_mono_on hT (intervalIntegrable_const (c := Real.exp (-2*|k| *T))) hc (fun s hs => ?_)
  · simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ) ≤ 2)
  · apply Real.exp_le_exp.mpr
    have hk : -|k| ≤ k := neg_abs_le k
    have hks : -2*|k| *s ≤ 2*k*s := by nlinarith [hs.1]
    have hst : -2*|k| *T ≤ -2*|k| *s := mul_le_mul_of_nonpos_left hs.2 (by nlinarith [abs_nonneg k])
    exact hst.trans hks
end WeakHessian

end
end InlinedFile213

end OAI
