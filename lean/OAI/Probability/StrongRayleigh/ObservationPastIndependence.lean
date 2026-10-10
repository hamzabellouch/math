import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.ObservationPastSupport

theorem indepFun_snd_signal_past
    {S : Type u_1} {Ω : Type u_2} {E : Type u_3} {H : Type u_4} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace H]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {Q : Ω → E} {history : Ω → H}
    (hQ : Measurable Q) (hhistory : Measurable history)
    (hind : IndepFun Q history P) :
    IndepFun (fun ω : S × Ω => Q ω.2)
      (fun ω : S × Ω => (ω.1, history ω.2)) (μ.prod P) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hpair : Measurable (fun ω : S × Ω => (ω.1, history ω.2)) := by fun_prop
  have hleft : Measurable (fun ω : S × Ω => Q ω.2) := by fun_prop
  rw [Measure.prod_apply ((hleft hs).inter (hpair ht)),
    Measure.prod_apply (hleft hs), Measure.prod_apply (hpair ht)]
  have hsection (a : S) :
      P (Prod.mk a ⁻¹' ((fun ω : S × Ω => Q ω.2) ⁻¹' s ∩
        (fun ω : S × Ω => (ω.1, history ω.2)) ⁻¹' t)) =
      P (Q ⁻¹' s) * P (history ⁻¹' (Prod.mk a ⁻¹' t)) := by
    exact hind.measure_inter_preimage_eq_mul s (Prod.mk a ⁻¹' t) hs
      (measurable_prodMk_left ht)
  simp_rw [hsection]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
  change _ = (∫⁻ (_ : S), P (Q ⁻¹' s) ∂μ) *
    ∫⁻ (a : S), P (history ⁻¹' (Prod.mk a ⁻¹' t)) ∂μ
  simp

theorem indepFun_snd_observation
    {S : Type u_5} {Ω : Type u_6} {E : Type u_7} {H : Type u_8} {Y : Type u_9}
    [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {Q : Ω → E} {history : Ω → H} (observe : S × H → Y)
    (hQ : Measurable Q) (hhistory : Measurable history)
    (hind : IndepFun Q history P) (hobserve : Measurable observe) :
    IndepFun (fun ω : S × Ω => Q ω.2)
      (fun ω : S × Ω => observe (ω.1, history ω.2)) (μ.prod P) := by
  exact (indepFun_snd_signal_past μ P hQ hhistory hind).comp measurable_id hobserve

theorem condExp_snd_observation
    {S : Type u_10} {Ω : Type u_11} {H : Type u_12} {Y : Type u_13} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {Q : Ω → ℝ} {history : Ω → H} (observe : S × H → Y)
    (hQ : Measurable Q) (hhistory : Measurable history)
    (hind : IndepFun Q history P) (hobserve : Measurable observe) :
    (μ.prod P)[(fun ω : S × Ω => Q ω.2) |
      MeasurableSpace.comap (fun ω : S × Ω => observe (ω.1, history ω.2)) inferInstance]
      =ᵐ[μ.prod P] fun _ => ∫ ω, Q ω ∂P := by
  have hQl : Measurable (fun ω : S × Ω => Q ω.2) := by fun_prop
  have hO : Measurable (fun ω : S × Ω => observe (ω.1, history ω.2)) := by fun_prop
  have h := condExp_indep_eq hQl.comap_le hO.comap_le
    (comap_measurable (fun ω : S × Ω => Q ω.2)).stronglyMeasurable
    (indepFun_snd_observation μ P observe hQ hhistory hind hobserve)
  simpa [integral_fun_snd] using h

theorem brownianShift_indep_observationHistory
    {S : Type u_14} {Ω : Type u_15} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X) (u : ℝ≥0) :
    IndepFun (fun ω : S × Ω => fun t : ℝ≥0 => B (u + t) ω.2 - B u ω.2)
      (fun ω : S × Ω => fun t : Set.Iic u => (t : ℝ) * X ω.1 + B t ω.2)
      (μ.prod P) := by
  exact indepFun_snd_observation μ P
    (fun z : S × (Set.Iic u → ℝ) => fun t : Set.Iic u => (t : ℝ) * X z.1 + z.2 t)
    (by fun_prop) (by fun_prop) (hB.indepFun_shift u) (by fun_prop)

theorem brownianIncrement_indep_observationHistory
    {S : Type u_16} {Ω : Type u_17} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X) (u v : ℝ≥0) :
    IndepFun (fun ω : S × Ω => B (u + v) ω.2 - B u ω.2)
      (fun ω : S × Ω => fun t : Set.Iic u => (t : ℝ) * X ω.1 + B t ω.2)
      (μ.prod P) := by
  exact (brownianShift_indep_observationHistory μ P hB hmB hX u).comp
    (measurable_pi_apply v) measurable_id

end Problem336AdditiveD139.ObservationPastSupport

end

end OAI
