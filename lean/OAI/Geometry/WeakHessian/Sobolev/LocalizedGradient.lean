import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolev
import OAI.Geometry.WeakHessian.LocalBounds.DuhamelAlgebra
import OAI.Geometry.WeakHessian.HeatFlow.HeatBridge

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.heatBridge_bounds {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeEnergy h f ξ T 0 ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T s ∧
    heatBridgeEnergy h f ξ T s ≤ Real.exp (2*(|K|+a*CG)*T)*heatBridgeEnergy h f ξ T T := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have htt : 0 ≤ T-s := sub_nonneg.mpr hs.2
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hfs : Sobolev ν (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hnfin hID).mpr
    ((cheegerHeat_energy_le h htt f).trans_lt ((identified_sobolev_iff_energy hnfin hID).mp hf))
  have hcomp (u : Lp ℝ 2 ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
      cheegerHeat h p (cheegerHeat h q u) = cheegerHeat h (p+q) u := by
    rw [cheegerHeat_add h hp hq]; rfl
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hb : 0 ≤ 2*(|K|+a*CG) := by positivity
  have hexp {p : ℝ} (hp : p ∈ Icc 0 T) :
      Real.exp (-(2*(K-a*CG))*p) ≤ Real.exp (2*(|K|+a*CG)*T) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ 2*(|K|+a*CG)*p := mul_le_mul_of_nonneg_right (by linarith [neg_le_abs K]) hp.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hp.2 hb
  constructor
  · have H := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o hF hFb hGb hGc ha h
      hfs hCξ hξb hξ0 hs.1
    rw [hcomp f hs.1 htt,add_sub_cancel] at H
    rw [heatBridgeEnergy_zero]
    exact H.trans (mul_le_mul_of_nonneg_right (hexp hs) (heatBridgeEnergy_nonneg h f ξ hξ0 T hs.1))
  · have H := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o hF hFb hGb hGc ha h
      hf hCξ (cheegerHeat_bounded h hs.1 hCξ ξ hξb) (cheegerHeat_nonneg h hs.1 ξ hξ0) htt
    rw [hcomp ξ htt hs.1,sub_add_cancel] at H
    rw [heatBridgeEnergy_end]
    exact H.trans (mul_le_mul_of_nonneg_right (hexp ⟨htt,by linarith [hs.1]⟩)
      (by simpa only [heatBridgeEnergy_end] using heatBridgeEnergy_nonneg h f ξ hξ0 T hT))

lemma WeakHessianUpperBound.localized_heat_gradient {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let M := Real.exp (2*(|K|+a*CG)*T)
    let κ := K-a*c
    let E := heatBridgeEnergy h f ξ T
    let D := heatBridgeError h f ξ (fun x => max (G x-c) 0) T
    IntervalIntegrable E volume 0 T ∧ IntervalIntegrable D volume 0 T ∧
      ((1+2*max κ 0*T/M)/(1+2*max (-κ) 0*T*M))*E 0 ≤
        E T+(2*a/(1+2*max (-κ) 0*T*M))*(∫ s in 0..T,D s) := by
  dsimp only
  let ν := exponentialMeasure m (fun x => a*F x)
  let J := fun x => max (G x-c) 0
  let κ := K-a*c
  let E := heatBridgeEnergy h f ξ T
  let D := heatBridgeError h f ξ J T
  let Z := heatBridgeError h f ξ (fun x => κ-a*J x) T
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hJc : Continuous J := (hGc.sub continuous_const).max continuous_const
  have hJb (x : X) : |J x| ≤ CG+|c| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [(abs_le.mp (hGb x)).2,neg_le_abs c]
    · positivity
  have hmaxb (x : X) : |max (G x) c| ≤ CG+|c| := abs_max_le_of_abs_le (hGb x)
  have hHmax := hHess.mono_bounded hfin hGc.aestronglyMeasurable
    (hGc.max continuous_const).aestronglyMeasurable hGb hmaxb (fun x => le_max_left (G x) c)
  have hki (x : X) : K-a*max (G x) c = κ-a*J x := by
    dsimp [κ,J]
    rcases le_total c (G x) with hc|hc
    · rw [max_eq_left hc,max_eq_left (sub_nonneg.mpr hc)]; ring
    · rw [max_eq_right hc,max_eq_right (sub_nonpos.mpr hc)]; ring
  have HZ := hHmax.rcd_weighted_heat_variable_sobolev hN hrcd hfull hfin o hF hFb hmaxb
    (hGc.max continuous_const) ha.le h hf hCξ hξb hξ0 hT
  simp_rw [hki] at HZ
  change IntervalIntegrable Z volume 0 T ∧ 2*(∫ s in 0..T,Z s) ≤ _ at HZ
  have hEi := hHess.heatBridge_integrable hN hrcd hfull hfin o hF hFb hGb hGc ha h hf hCξ hξb hξ0 hT
  change IntervalIntegrable E volume 0 T at hEi
  have hdecomp (s : ℝ) (hs : s ∈ Icc 0 T) : Z s = κ*E s-a*D s :=
    heatBridgeError_decompose hnfin hID h hf hCξ hξb hJc.aestronglyMeasurable
      (ae_of_all _ hJb) κ a T hs
  have hDi : IntervalIntegrable D volume 0 T := by
    have H := ((hEi.const_mul κ).sub HZ.1).const_mul a⁻¹
    apply (intervalIntegrable_congr ?_).mp H
    intro s hs
    rw [uIoc_of_le hT] at hs
    change a⁻¹*(κ*E s-Z s) = D s
    rw [hdecomp s ⟨hs.1.le,hs.2⟩]
    field_simp
    ring
  refine ⟨hEi,hDi,?_⟩
  have hint : (∫ s in 0..T,Z s) = κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s) := by
    calc
      _ = ∫ s in 0..T,κ*E s-a*D s := intervalIntegral.integral_congr (by
        rw [uIcc_of_le hT]; exact hdecomp)
      _ = _ := by rw [intervalIntegral.integral_sub (hEi.const_mul κ) (hDi.const_mul a),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hduh := HZ.2
  rw [hint,← heatBridgeEnergy_end h f ξ T,← heatBridgeEnergy_zero h f ξ T] at hduh
  apply duhamel_signed_error_ratio hT (Real.exp_pos _) hEi
    (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).1)
    (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).2)
    hduh

end WeakHessian

end
end

end OAI
