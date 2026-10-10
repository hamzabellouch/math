import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedBE
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatInterpolation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile193
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_interpolation_BE {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Bξ x| ≤ CBξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    2*(∫ x,(cheegerHeat h t ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      deriv (fun s => ∫ x,cheegerHeat h s ξ x*
        gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
          ∂exponentialMeasure m (fun x => a*F x)) t := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hd := hrcd.weighted_heat_interpolation_hasDerivAt hN hfull hfin o hV hVB h hf hAf hξ hBξ
    hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb ht htT
  rw [hd.deriv]
  have hgen {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν hu s)
  have hBE := hHess.rcd_weighted_BE hN hrcd hfull hfin o hF hFb hGb hGc ha
    (hgen hf (T-t)) (hgen hAf (T-t)).1 (hgen hξ t)
    (cheegerHeat_bounded h ht.le hCξ ξ hξb) (cheegerHeat_bounded h ht.le hCBξ Bξ hBξb)
    (cheegerHeat_nonneg h ht.le ξ hξ0)
  linarith only [hBE]
end WeakHessian

end
end InlinedFile193

end OAI
