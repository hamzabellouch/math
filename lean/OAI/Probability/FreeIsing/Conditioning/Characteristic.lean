import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConditionalCharacteristic

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

def character (X : Ω → ℝ) (t : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (t * X ω * Complex.I)

theorem measurable_character {X : Ω → ℝ} (hX : Measurable[mΩ] X) (t : ℝ) :
    Measurable (character X t) := by
  unfold character
  fun_prop

theorem integrable_character {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (t : ℝ) :
    Integrable (character X t) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_character hX t).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp [character, ← Complex.ofReal_mul]

theorem map_restrict_eq_smul_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    Measure.map X (P.restrict s) = P s • ν := by
  let : IsFiniteMeasure (P s • ν) := ν.smul_finite (measure_ne_top P s)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop),
    charFun_apply_real, integral_smul_measure]
  change (∫ ω in s, character X t ω ∂P) = _
  rw [← setIntegral_condExp hm (integrable_character hX t) hs]
  calc
    (∫ ω in s, P[character X t | m] ω ∂P) =
        ∫ _ in s, charFun ν t ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hchar t))
    _ = _ := by simp [charFun_apply_real, measureReal_def]

theorem map_eq_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t) :
    Measure.map X P = ν := by
  simpa using map_restrict_eq_smul_of_condExp_character hm hX ν hchar
    (MeasurableSet.univ : MeasurableSet[m] Set.univ)

theorem indepFun_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t)
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    IndepFun X Y P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro a b ha hb
  have hrestrict := congrArg (fun μ : Measure ℝ => μ a)
    (map_restrict_eq_smul_of_condExp_character hm hX ν hchar (hY hb))
  have hlaw := map_eq_of_condExp_character hm hX ν hchar
  rw [Measure.map_apply hX ha, Measure.restrict_apply (hX ha),
    Measure.smul_apply, smul_eq_mul, ← hlaw, Measure.map_apply hX ha] at hrestrict
  exact hrestrict.trans (mul_comm _ _)

theorem hasLaw_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t) :
    HasLaw X ν P :=
  ⟨hX.aemeasurable, map_eq_of_condExp_character hm hX ν hchar⟩

theorem gaussian_law_and_indep_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (v : ℝ≥0)
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P]
      fun _ => Complex.exp (-((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (gaussianReal 0 v) P ∧ IndepFun X Y P := by
  have hc : ∀ t : ℝ, P[character X t | m] =ᵐ[P]
      fun _ => charFun (gaussianReal 0 v) t := by
    intro t
    simpa only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      neg_mul, neg_div] using hchar t
  exact ⟨hasLaw_of_condExp_character hm hX _ hc,
    indepFun_of_condExp_character hm hX _ hc hY⟩

end Problem367.ConditionalCharacteristic

end

end OAI
