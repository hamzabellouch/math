import Mathlib
import OAI.Geometry.WeakHessian.Transport.RestrictCurve
import OAI.Geometry.WeakHessian.Transport.ActionIntervalIntegrable

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma evalReal_coe (γ : Curve X) (t : Time) : evalReal γ (t : ℝ) = γ t := by
  apply congrArg γ
  apply Subtype.ext
  simp only [clampTime, min_eq_right t.property.2, max_eq_right t.property.1]

lemma IsLocalWeakUpperGradient.ae_deriv_comp_le {f D : X → ℝ} {L : ℝ≥0}
    (hD : IsLocalWeakUpperGradient m f D) (hf : LipschitzWith L f)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
        ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  let : Nonempty Time := ⟨timeZero⟩
  let d : ℕ → Time := TopologicalSpace.denseSeq Time
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  let a : Curve X × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2
  have ham : AEMeasurable a (π.prod ν) := hπ.aemeasurable_action hD.1
  have hameq := Measure.ae_ae_eq_curry_of_prod ham.ae_eq_mk
  have hafin := ae_lt_top' ham.lintegral_prod_right' (hπ.lintegral_action_lt_top hb hD.1).ne
  have hbnd : ∀ᵐ γ ∂π, ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |f (γ (d j)) - f (γ (d i))| ≤
        ∫⁻ t in Set.Icc (d i : ℝ) (d j : ℝ), a (γ,t) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : (d i : ℝ) < d j
    · exact (hD.ae_subinterval_le hf.continuous.measurable.aemeasurable hπ hb (d i) (d j) hij).mono
        (fun _ h => fun _ => h)
    · exact ae_of_all _ fun _ h => (hij h).elim
  filter_upwards [hameq, hafin, hbnd, hπ.2.2.1] with γ hameq hafin hbnd hγ
  have hamγ : AEMeasurable (fun t => a (γ,t)) ν :=
    (ham.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr hameq.symm
  apply WeakHessianCalculus.ae_deriv_le_of_dense_action
    (lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous) hamγ hafin d hd
  intro i j hij
  simpa only [evalReal_coe] using hbnd i j hij

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma LocallyL2.min {D E : X → ℝ} (hD : LocallyL2 m D) (hE : LocallyL2 m E) :
    LocallyL2 m (fun x => min (D x) (E x)) :=
  fun o R hR => (hD o R hR).inf (hE o R hR)

lemma IsLocalWeakUpperGradient.min {f D E : X → ℝ} {L : ℝ≥0}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m f E)
    (hf : LipschitzWith L f) : IsLocalWeakUpperGradient m f (fun x => Min.min (D x) (E x)) := by
  refine ⟨hD.1.min hE.1, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with x hx hy
    exact le_min hx hy
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_deriv_comp_le hf hπ hb, hE.ae_deriv_comp_le hf hπ hb,
      hπ.2.2.1] with γ hd he hγ
    have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
        simp [evalReal, clampTime, timeOne, timeZero]
        rfl
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (Min.min (D (evalReal γ t)) (E (evalReal γ t))) * metricSpeed γ t := by
        apply lintegral_mono_ae
        filter_upwards [hd, he] with t hdt het
        rcases le_total (D (evalReal γ t)) (E (evalReal γ t)) with h|h
        · simpa only [min_eq_left h, Real.enorm_eq_ofReal_abs] using hdt
        · simpa only [min_eq_right h, Real.enorm_eq_ofReal_abs] using het

end WeakHessian

end
end InlinedFile0

end OAI
