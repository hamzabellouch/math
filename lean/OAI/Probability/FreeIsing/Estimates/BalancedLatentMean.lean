import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Estimates.LatentProductIndependence
import OAI.Probability.FreeIsing.Spins.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

private theorem integrable_of_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2)

theorem integral_binary_channel_le_two_integral
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (a : IsingSpin) :
    (∫ r, F (a, r) ∂ν) ≤
      2 * ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
  let : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
  let E : Set S := {s | b s = a}
  let q : S → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_eq_fun hb measurable_const
  have hq : Measurable q := measurable_const.indicator hE
  have hleft : Measurable (fun z : S × A => q z.1 * F (a, z.2)) :=
    (hq.comp measurable_fst).mul (hF.comp (measurable_const.prodMk measurable_snd))
  have hright : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hleftbound : ∀ z : S × A,
      0 ≤ q z.1 * F (a, z.2) ∧ q z.1 * F (a, z.2) ≤ 1 := by
    intro z
    by_cases hz : b z.1 = a
    · simpa [q, E, hz] using hbound (a, z.2)
    · simp [q, E, hz]
  have hmono := integral_mono
    (integrable_of_unit_bounds (ρ.prod ν) hleft hleftbound)
    (integrable_of_unit_bounds (ρ.prod ν) hright (fun z => hbound (b z.1, z.2)))
    (show ∀ z : S × A, q z.1 * F (a, z.2) ≤ F (b z.1, z.2) from by
      intro z
      by_cases hz : b z.1 = a
      · simp [q, E, hz]
      · simpa [q, E, hz] using (hbound (b z.1, z.2)).1)
  have hmass : (∫ s, q s ∂ρ) = (1 / 2 : ℝ) := by
    rw [show q = E.indicator (fun _ => 1) from rfl, integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one, Measure.real, E, hfair]
    norm_num
  rw [integral_prod_mul q (fun r => F (a, r)), hmass] at hmono
  linarith

theorem condExp_binary_channel_le_two_integral
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂ρ.prod ν,
      ((ρ.prod ν)[(fun z : S × A => F (b z.1, z.2)) | mS.comap Prod.fst]) z ≤
        2 * ∫ w : S × A, F (b w.1, w.2) ∂ρ.prod ν := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  filter_upwards [condExp_prod_fst ρ ν hm.stronglyMeasurable hi] with z hz
  rw [hz]
  exact integral_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound (b z.1)

theorem condExp_binary_channel_comp_le_two_integral
    {Ω S A : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace A]
    (μ : Measure Ω) (ρ : Measure S) (ν : Measure A)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (e : Ω → S × A) (he : MeasurePreserving e μ (ρ.prod ν))
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ ω ∂μ,
      (μ[(fun ω => F (b (e ω).1, (e ω).2)) |
        mS.comap (fun ω => (e ω).1)]) ω ≤
          2 * ∫ x, F (b (e x).1, (e x).2) ∂μ := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  have hpull := condExp_comp_measurePreserving μ (ρ.prod ν) e he
    (mS.comap Prod.fst) measurable_fst.comap_le hi
  have hboundpull := he.quasiMeasurePreserving.ae
    (condExp_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound)
  have hint : (∫ x, F (b (e x).1, (e x).2) ∂μ) =
      ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable
      (hm.aestronglyMeasurable)).symm
  rw [hint]
  filter_upwards [hpull, hboundpull] with ω hω hωb
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hω.trans_le hωb

end Problem367

end

end OAI
