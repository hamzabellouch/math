import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GammaTimeDifferentiation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile192
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma cheegerHeat_backwards_derivative (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t T : ℝ} (ht : t < T) :
    HasDerivAt (fun s => cheegerHeat h (T-s) u) (-cheegerHeat h (T-t) A) t := by
  have H := (cheegerHeat_deriv_at_generator hfin h hu (sub_pos.mpr ht)).scomp_of_eq t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t)) rfl
  simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,id_eq,Pi.sub_apply] using H

lemma RCD.weighted_heat_interpolation_hasDerivAt {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m V)}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m V,|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m V,|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m V,|Bξ x| ≤ CBξ)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ x,cheegerHeat h s ξ x*
        gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
          ∂exponentialMeasure m V)
      ((∫ x,cheegerHeat h t Bξ x*
        gamma (exponentialMeasure m V) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) f) x
          ∂exponentialMeasure m V)-
        2*(∫ x,cheegerHeat h t ξ x*
          gamma (exponentialMeasure m V) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) Af) x
            ∂exponentialMeasure m V)) t := by
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hgen {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr (Q.formGenerator_heat ν hu s)
  obtain ⟨n,hn⟩ := exists_nat_ge (max Cf CAf)
  have hn1 : Cf ≤ (n:ℝ) := (le_max_left _ _).trans hn
  have hn2 : CAf ≤ (n:ℝ) := (le_max_right _ _).trans hn
  apply hasDerivAt_gamma_interpolation (Cξ := Cξ) (CB := CBξ) hnfin hnpar
    (cheegerHeat_backwards_derivative hnfin h hf htT)
    (cheegerHeat_backwards_derivative hnfin h hAf htT)
    (cheegerHeat_deriv_at_generator hnfin h hξ ht)
    (cheegerHeat_deriv_at_generator hnfin h hBξ ht)
    (Eventually.of_forall fun s => hgen hf (T-s)) (hgen hAf (T-t))
    (Eventually.of_forall fun s => hgen hξ s) (hgen hBξ t)
    _ _ n _ _ _ (cheegerHeat_bounded h ht.le hCBξ Bξ hBξb)
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hf hCf hCAf
      hfb hAfb (sub_nonneg.mpr hs.le)
  · exact hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hAf hCAf hCAAf
      hAfb hAAfb (sub_nonneg.mpr htT.le)
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact (cheegerHeat_bounded h (sub_nonneg.mpr hs.le) hCf f hfb).mono fun x hx => hx.trans hn1
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact (cheegerHeat_bounded h (sub_nonneg.mpr hs.le) hCAf Af hAfb).mono fun x hx => hx.trans hn2
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact cheegerHeat_bounded h hs.le hCξ ξ hξb
end WeakHessian

end
end InlinedFile192

end OAI
