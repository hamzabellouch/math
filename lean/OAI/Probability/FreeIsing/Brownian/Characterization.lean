import OAI.Probability.FreeIsing.Conditioning.Characteristic

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.BrownianCharacterization

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condExp_character_of_setIntegral
    (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X) (c : ℂ) (u : ℝ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A →
      (∫ ω in A, character X u ω ∂μ) = μ.real A * c) :
    μ[character X u | m] =ᵐ[μ] fun _ => c := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (integrable_character hX u)
  · intro A _ _
    exact (integrable_const c).integrableOn
  · intro A hA _
    rw [hchar A hA]
    simp
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem hasIndepIncrements_of_past_events_general
    {T E : Type*} [Preorder T] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {B : T → Ω → E} (F : Filtration T mΩ) (hB : Adapted F B)
    (hind : ∀ s t : T, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ S : Set E, MeasurableSet S →
        μ (A ∩ (fun ω => B t ω - B s ω) ⁻¹' S) =
          μ A * μ ((fun ω => B t ω - B s ω) ⁻¹' S)) :
    HasIndepIncrements B μ := by
  intro n t ht
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    intro hsets
    have ha : a ∉ S := by
      intro ha
      exact lt_irrefl a (hlt a ha)
    have hmsets : ∀ i ∈ S, MeasurableSet (sets i) :=
      fun i hi => hsets i (Finset.mem_insert_of_mem hi)
    have hA : MeasurableSet[F (t a.castSucc)]
        (⋂ i ∈ S, (fun ω => B (t i.succ) ω - B (t i.castSucc) ω) ⁻¹' sets i) := by
      apply S.measurableSet_biInter
      intro i hi
      have hi1 : t i.succ ≤ t a.castSucc := ht (by
        change i.val + 1 ≤ a.val
        exact Nat.succ_le_of_lt (hlt i hi))
      have hi0 : t i.castSucc ≤ t a.castSucc := ht (by
        change i.val ≤ a.val
        exact (hlt i hi).le)
      exact ((hB.measurable_le hi1).sub (hB.measurable_le hi0)) (hmsets i hi)
    have h := hind (t a.castSucc) (t a.succ) (ht (by change a.val ≤ a.val + 1; omega)) _ hA
      (sets a) (hsets a (Finset.mem_insert_self a S))
    rw [Finset.prod_insert ha]
    rw [Finset.set_biInter_insert]
    rw [Set.inter_comm, h, ih hmsets, mul_comm]

theorem hasIndepIncrements_of_past_events
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B)
    (hind : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ S : Set ℝ, MeasurableSet S →
        μ (A ∩ (fun ω => B t ω - B s ω) ⁻¹' S) =
          μ A * μ ((fun ω => B t ω - B s ω) ⁻¹' S)) :
    HasIndepIncrements B μ :=
  hasIndepIncrements_of_past_events_general F hB.adapted hind

theorem hasIndepIncrements_of_conditional_increment_laws
    {T E : Type*} [Preorder T] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {B : T → Ω → E} (F : Filtration T mΩ) (hB : Adapted F B)
    (ν : T → T → Measure E)
    (hlaw : ∀ s t : T, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      (μ.restrict A).map (fun ω => B t ω - B s ω) = μ A • ν s t) :
    HasIndepIncrements B μ := by
  apply hasIndepIncrements_of_past_events_general F hB
  intro s t hst A hA S hS
  have hm : Measurable (fun ω => B t ω - B s ω) :=
    hB.measurable.sub hB.measurable
  have huniv : μ.map (fun ω => B t ω - B s ω) = ν s t := by
    simpa using hlaw s t hst Set.univ MeasurableSet.univ
  have h := congrArg (fun κ : Measure E => κ S) (hlaw s t hst A hA)
  rw [Measure.map_apply hm hS, Measure.restrict_apply (hm hS),
    Measure.smul_apply, smul_eq_mul, ← huniv, Measure.map_apply hm hS] at h
  simpa only [Set.inter_comm] using h

theorem isPreBrownianReal_of_conditional_charFun
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ u : ℝ,
      μ[character (fun ω => B t ω - B s ω) u | F s]
        =ᵐ[μ] fun _ => charFun (gaussianReal 0 (t - s)) u) :
    IsPreBrownianReal B μ := by
  have hm (t : ℝ≥0) : Measurable (B t) := ((hB t).mono (F.le t)).measurable
  have hlaw (s t : ℝ≥0) (hst : s ≤ t) :
      HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) μ :=
    hasLaw_of_condExp_character (F.le s) ((hm t).sub (hm s)) _ (hchar s t hst)
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    have h := hlaw 0 t (by positivity)
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [hzero] with ω hω
    simp [hω]
  · apply hasIndepIncrements_of_past_events F hB
    intro s t hst A hA S hS
    have hmap := map_restrict_eq_smul_of_condExp_character (F.le s)
      ((hm t).sub (hm s)) (gaussianReal 0 (t - s)) (hchar s t hst) hA
    have h := congrArg (fun κ : Measure ℝ => κ S) hmap
    rw [Measure.map_apply ((hm t).sub (hm s)) hS,
      Measure.restrict_apply (((hm t).sub (hm s)) hS),
      Measure.smul_apply, smul_eq_mul] at h
    have hmass : μ ((fun ω => B t ω - B s ω) ⁻¹' S) = gaussianReal 0 (t - s) S := by
      rw [← (hlaw s t hst).map_eq]
      exact (Measure.map_apply (show Measurable (fun ω => B t ω - B s ω) from
        (hm t).sub (hm s)) hS).symm
    rw [hmass, Set.inter_comm]
    exact h

theorem isPreBrownianReal_of_conditional_exponential
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ u : ℝ,
      μ[character (fun ω => B t ω - B s ω) u | F s] =ᵐ[μ]
        fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2)) :
    IsPreBrownianReal B μ := by
  apply isPreBrownianReal_of_conditional_charFun F hB hzero
  intro s t hst u
  simpa only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub, neg_mul, neg_div] using hchar s t hst u

theorem isPreBrownianReal_of_setIntegral_character
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ u : ℝ, (∫ ω in A, character (fun ω => B t ω - B s ω) u ω ∂μ) =
        μ.real A * Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2)) :
    IsPreBrownianReal B μ := by
  apply isPreBrownianReal_of_conditional_exponential F hB hzero
  intro s t hst u
  exact condExp_character_of_setIntegral (F.le s)
    (((hB t).mono (F.le t)).measurable.sub ((hB s).mono (F.le s)).measurable)
    _ u (fun A hA => hchar s t hst A hA u)

theorem isBrownianReal_of_setIntegral_character
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hcontinuous : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω))
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ u : ℝ, (∫ ω in A, character (fun ω => B t ω - B s ω) u ω ∂μ) =
        μ.real A * Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2)) :
    IsBrownianReal B μ :=
  ⟨isPreBrownianReal_of_setIntegral_character F hB hzero hchar, hcontinuous⟩

end Problem367.BrownianCharacterization

end

end OAI
