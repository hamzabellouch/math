import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EvalRealCoe
import OAI.Geometry.WeakHessian.LocalBounds.AbsolutelyContinuousDistDom

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLocalWeakUpperGradient.ae_action_data {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π,
      AEMeasurable (fun t => ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)
        (volume.restrict (Icc (0 : ℝ) 1)) ∧
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let a : Curve X × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2
  have ham : AEMeasurable a (π.prod ν) := hπ.aemeasurable_action hD.1
  have hameq := Measure.ae_ae_eq_curry_of_prod ham.ae_eq_mk
  have hafin := ae_lt_top' ham.lintegral_prod_right' (hπ.lintegral_action_lt_top hb hD.1).ne
  filter_upwards [hameq, hafin] with γ hameq hafin
  exact ⟨(ham.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr hameq.symm, hafin⟩

lemma IsLocalWeakUpperGradient.ae_dense_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (d : ℕ → Time) :
    ∀ᵐ γ ∂π, ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |f (γ (d j)) - f (γ (d i))| ≤
        ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : (d i : ℝ) < d j
  · exact (hD.ae_subinterval_le hf hπ hb (d i) (d j) hij).mono (fun _ h => fun _ => h)
  · exact ae_of_all _ fun _ h => (hij h).elim

lemma IsLocalWeakUpperGradient.min_measurable {f D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m f E)
    (hf : AEMeasurable f m) : IsLocalWeakUpperGradient m f (fun x => Min.min (D x) (E x)) := by
  refine ⟨hD.1.min hE.1, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with x hx hy
    exact le_min hx hy
  · intro π hπ hb
    let : Nonempty Time := ⟨timeZero⟩
    let d : ℕ → Time := fun n => match n with
      | 0 => timeZero
      | 1 => timeOne
      | n + 2 => TopologicalSpace.denseSeq Time n
    have hd : DenseRange d := by
      apply DenseRange.of_comp (g := fun n => n + 2)
      exact TopologicalSpace.denseRange_denseSeq Time
    apply lintegral_mono_ae
    filter_upwards [hD.ae_action_data hπ hb, hE.ae_action_data hπ hb,
      hD.ae_dense_subinterval_le hf hπ hb d, hE.ae_dense_subinterval_le hf hπ hb d]
      with γ hDa hEa hDb hEb
    have hDb' : ∀ i j, (d i : ℝ) < d j →
        ENNReal.ofReal |f (evalReal γ (d j)) - f (evalReal γ (d i))| ≤
          ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
            ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
      simpa only [evalReal_coe] using hDb
    obtain ⟨q,hq,heq⟩ := WeakHessianCalculus.exists_ac_representative (q := fun t => f (evalReal γ t)) hDa.1 hDa.2 d hDb'
    have hqd : ∀ i, q (d i) = f (γ (d i)) := by
      simpa only [evalReal_coe] using heq
    have hqd0 : q 0 = f (γ timeZero) := hqd 0
    have hqd1 : q 1 = f (γ timeOne) := hqd 1
    have hdD := WeakHessianCalculus.ae_deriv_le_of_dense_action hq hDa.1 hDa.2 d hd
      (by simpa only [hqd] using hDb)
    have hdE := WeakHessianCalculus.ae_deriv_le_of_dense_action hq hEa.1 hEa.2 d hd
      (by simpa only [hqd] using hEb)
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv q t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hq.integral_deriv_eq_sub, hqd0, hqd1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv q t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (Min.min (D (evalReal γ t)) (E (evalReal γ t))) * metricSpeed γ t := by
        apply lintegral_mono_ae
        filter_upwards [hdD, hdE] with t hdt het
        rcases le_total (D (evalReal γ t)) (E (evalReal γ t)) with h|h
        · simpa only [min_eq_left h, Real.enorm_eq_ofReal_abs] using hdt
        · simpa only [min_eq_right h, Real.enorm_eq_ofReal_abs] using het

end WeakHessian

end
end InlinedFile0

end OAI
