import OAI.Analysis.KadisonKastler.RegularCoreFields

namespace OAI

/-! # Fixed decomposable operators in the regular representation

The gauge transforms a decomposable operator fixed by `U_s ⊗ ρ_s` into
a translation-fixed multiplier. The preceding scalar Fubini argument
then makes it a constant operator, so the original operator belongs to
the concrete regular image `π(B(H))`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- The gauge conjugation has the expected field formula. -/
theorem RepresentsOperatorField.regular_gauge
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) :
    RepresentsOperatorField volume
      (fun t => unitaryConj (U (Multiplicative.ofAdd t)) (F t))
      (unitaryConj (regularGauge U hU) T) := by
  intro f
  filter_upwards [regularGauge_apply_ae U hU
      (T ((star (regularGauge U hU) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    hF ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae U hU f] with t hg hT hgs
  change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (T ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hg, hT, hgs]
  rfl

/-- Fixedness passes through the exact gauge intertwining identity. -/
theorem regularGauge_translation_fixed
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hfixed : ∀ s, unitaryConj (regularCoreAction U s) T = T)
    (s : Multiplicative ℝ) :
    unitaryConj (regularRightTranslation (H := H) s)
      (unitaryConj (regularGauge U hU) T) = unitaryConj (regularGauge U hU) T := by
  have he : regularGauge U hU * regularCoreAction U s =
      regularRightTranslation (H := H) s * regularGauge U hU :=
    Subtype.ext (regularGauge_intertwines_action U hU s)
  rw [← unitaryConj_mul, ← he, unitaryConj_mul, hfixed]

/-- A weakly measurable decomposable operator fixed by the common action
belongs to the actual regular image. -/
theorem exists_regularCoreEmbedding_of_field_fixed [TopologicalSpace.SeparableSpace H]
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (hfixed : ∀ s, unitaryConj (regularCoreAction U s) T = T) :
    ∃ A : H →L[ℂ] H, T = regularCoreEmbedding U hU A := by
  let F' : ℝ → H →L[ℂ] H := fun t =>
    unitaryConj (U (Multiplicative.ofAdd t)) (F t)
  have hm (ξ : H) : AEStronglyMeasurable (fun t => F' t ξ) volume := by
    exact aestronglyMeasurable_field_apply
      (fun t => (U (Multiplicative.ofAdd t) : H →L[ℂ] H))
      (fun x => (hU x).aestronglyMeasurable)
      (fun t => F t ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ))
      (aestronglyMeasurable_field_apply F hmeas _
        (regularGroup_star_measurable U hU ξ))
  obtain ⟨A, _, hA⟩ := constant_of_regularField_translation_fixed
    (hF.regular_gauge U hU) hm (regularGauge_translation_fixed U hU hfixed)
  refine ⟨A, ?_⟩
  have he := congrArg (unitaryConj (star (regularGauge U hU))) hA
  rw [unitaryConj_star_unitaryConj] at he
  exact he

end

end KadisonKastler

end OAI
