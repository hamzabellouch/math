import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LocalizedGradient
import OAI.Geometry.WeakHessian.Transport.BridgeError

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def localizedHeatM (K a CG T : ℝ) : ℝ := Real.exp (2*(|K|+a*CG)*T)
def localizedHeatDen (K a c CG T : ℝ) : ℝ := 1+2*max (-(K-a*c)) 0*T*localizedHeatM K a CG T
def localizedHeatFactor (K a c CG T : ℝ) : ℝ :=
  (1+2*max (K-a*c) 0*T/localizedHeatM K a CG T)/localizedHeatDen K a c CG T

def localizedHeatError {m : Measure X} (h : QuadraticCheegerEnergy m) (ξ : Lp ℝ 2 m)
    (G : X → ℝ) (K a c CG T : ℝ) (f : Lp ℝ 2 m) : ℝ :=
  (2*a/localizedHeatDen K a c CG T)*(∫ s in 0..T,heatBridgeError h f ξ (fun x => max (G x-c) 0) T s)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedHeatDen_one_le (K a c CG : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ localizedHeatDen K a c CG T := by
  dsimp [localizedHeatDen,localizedHeatM]
  exact le_add_of_nonneg_right (by positivity)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedHeatFactor_pos (K a c CG : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 < localizedHeatFactor K a c CG T := by
  dsimp [localizedHeatFactor,localizedHeatDen,localizedHeatM]
  positivity

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.localized_heat_certificate {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let ν := exponentialMeasure m (fun x => a*F x)
    let R := localizedHeatError h ξ G K a c CG T
    let b := localizedHeatFactor K a c CG T
    (∀ f : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) →
      b*(∫ x,ξ x*(weakGradient ν (cheegerHeat h T f) x)^2 ∂ν) ≤
        (∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν)+R f) ∧
    (∀ f g : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) → Sobolev ν (g : X → ℝ) →
      ∀ t : ℝ,R (f+t•g) ≤ 2*R f+2*t^2*R g) ∧
    (∀ f : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) →
      0 ≤ R f ∧ R f ≤ 2*a*(CG+|c|)*T*localizedHeatM K a CG T*
        (∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν)) := by
  dsimp only
  let ν := exponentialMeasure m (fun x => a*F x)
  let J := fun x => max (G x-c) 0
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (exponentialMeasure_comparable (m := m) hVB).1 (exponentialMeasure_comparable (m := m) hVB).2
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hJm : AEStronglyMeasurable J ν := ((hGc.sub continuous_const).max continuous_const).aestronglyMeasurable
  have hJb : ∀ᵐ x ∂ν,|J x| ≤ CG+|c| := ae_of_all _ fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [(abs_le.mp (hGb x)).2,neg_le_abs c]
    · positivity
  have hJ0 : ∀ᵐ x ∂ν,0 ≤ J x := ae_of_all _ fun _ => le_max_right _ _
  have H := fun f hf => hHess.localized_heat_gradient hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (f := f) (ξ := ξ) hf hCξ hξb hξ0 c hT
  have hDi (f : Lp ℝ 2 ν) (hf : Sobolev ν (f : X → ℝ)) :
      IntervalIntegrable (heatBridgeError h f ξ J T) volume 0 T := (H f hf).2.1
  have hDn := localizedHeatDen_one_le K a c CG hT
  have hDp : 0 < localizedHeatDen K a c CG T := zero_lt_one.trans_le hDn
  have hθ : 0 ≤ 2*a/localizedHeatDen K a c CG T := by positivity
  have hθb : 2*a/localizedHeatDen K a c CG T ≤ 2*a := by
    apply (div_le_iff₀ hDp).mpr
    nlinarith
  have hend (f : Lp ℝ 2 ν) : heatBridgeEnergy h f ξ T T =
      ∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν := by
    rw [heatBridgeEnergy_end]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) f] with x hx
    rw [hx]
  refine ⟨?_,?_,?_⟩
  · intro f hf
    have Hf := (H f hf).2.2
    have hzero : heatBridgeEnergy h f ξ T 0 =
        ∫ x,ξ x*(weakGradient ν (cheegerHeat h T f) x)^2 ∂ν := by
      rw [heatBridgeEnergy_zero]
      apply integral_congr_ae
      filter_upwards [gamma_self (m := ν) (cheegerHeat h T f)] with x hx
      rw [hx]
    rw [hzero,hend] at Hf
    exact Hf
  · intro f g hf hg t
    have HH := mul_le_mul_of_nonneg_left
      (heatBridgeError_integral_split hnfin hID hpar h hf hg hCξ hξb hξ0 hJm hJb hJ0 hT hDi t) hθ
    dsimp [localizedHeatError]
    convert HH using 1
    first | rfl | ring
  · intro f hf
    have hIn : 0 ≤ ∫ s in 0..T,heatBridgeError h f ξ J T s :=
      intervalIntegral.integral_nonneg hT (fun s hs => heatBridgeError_nonneg h f ξ hξ0 hJ0 T hs.1)
    have hIb := heatBridgeError_integral_le hnfin hID h hf hCξ hξb hξ0 hJm
      (by positivity : 0 ≤ CG+|c|) hJb hT (hDi f hf)
      (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).2)
    refine ⟨mul_nonneg hθ hIn,?_⟩
    rw [hend] at hIb
    change (2*a/localizedHeatDen K a c CG T)*(∫ s in 0..T,heatBridgeError h f ξ J T s) ≤ _
    exact (mul_le_mul_of_nonneg_right hθb hIn).trans
      ((mul_le_mul_of_nonneg_left hIb (by positivity : 0 ≤ 2*a)).trans_eq (by dsimp [localizedHeatM]; ring))

end WeakHessian

end
end

end OAI
