import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace Problem336AdditiveD139.IndependentConditioning

variable {Ω : Type u_1} {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def fieldRectangles (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m₁] a ∧ MeasurableSet[m₂] b ∧ s = a ∩ b}

lemma isPiSystem_fieldRectangles (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (fieldRectangles m₁ m₂) := by
  rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨c, d, hc, hd, rfl⟩ _
  refine ⟨a ∩ c, b ∩ d, ha.inter hc, hb.inter hd, ?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto

lemma generateFrom_fieldRectangles (m₁ m₂ : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (fieldRectangles m₁ m₂) = m₁ ⊔ m₂ := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact ((show m₁ ≤ m₁ ⊔ m₂ from le_sup_left) a ha).inter
      ((show m₂ ≤ m₁ ⊔ m₂ from le_sup_right) b hb)
  · refine sup_le ?_ ?_
    · intro a ha
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨a, univ, ha, .univ, (inter_univ a).symm⟩
    · intro b hb
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨univ, b, .univ, hb, (univ_inter b).symm⟩

variable {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω}

lemma setIntegral_inter_of_indep [IsFiniteMeasure μ]
    (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m) (hind : Indep m₁ m₂ μ)
    {f : Ω → E} (hfm : StronglyMeasurable[m₁] f) (hfi : Integrable f μ)
    {a b : Set Ω} (ha : MeasurableSet[m₁] a) (hb : MeasurableSet[m₂] b) :
    ∫ x in a ∩ b, f x ∂μ = μ.real b • ∫ x in a, f x ∂μ := by
  have hi : Integrable (a.indicator f) μ := hfi.indicator (h₁ a ha)
  have he := condExp_indep_eq h₁ h₂ (hfm.indicator ha) hind
  have he' := setIntegral_congr_ae (h₂ b hb) (he.mono fun x hx _ => hx)
  rw [setIntegral_condExp h₂ hi hb, setIntegral_const,
    setIntegral_indicator (h₁ a ha), integral_indicator (h₁ a ha)] at he'
  simpa only [inter_comm] using he'

omit [CompleteSpace E] in

lemma setIntegral_eq_of_fieldRectangles
    (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m) {f g : Ω → E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hrect : ∀ a b, MeasurableSet[m₁] a → MeasurableSet[m₂] b →
      ∫ x in a ∩ b, f x ∂μ = ∫ x in a ∩ b, g x ∂μ) :
    ∀ s, MeasurableSet[m₁ ⊔ m₂] s →
      ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ := by
  have hsup : m₁ ⊔ m₂ ≤ m := sup_le h₁ h₂
  have htotal : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
    simpa using hrect univ univ .univ .univ
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (generateFrom_fieldRectangles m₁ m₂).symm
    (isPiSystem_fieldRectangles m₁ m₂) ?_ ?_ ?_ ?_
  · simp
  · rintro s ⟨a, b, ha, hb, rfl⟩
    exact hrect a b ha hb
  · intro s hs ih
    rw [setIntegral_compl (hsup s hs) hf, setIntegral_compl (hsup s hs) hg,
      htotal, ih]
  · intro s hdisj hmeas ih
    rw [integral_iUnion (fun n => hsup _ (hmeas n)) hdisj hf.integrableOn,
      integral_iUnion (fun n => hsup _ (hmeas n)) hdisj hg.integrableOn]
    exact tsum_congr ih

theorem condExp_sup_of_indep [IsFiniteMeasure μ]
    {mX mY mZ : MeasurableSpace Ω}
    (hX : mX ≤ m) (hZ : mZ ≤ m) (hYX : mY ≤ mX)
    (hind : Indep mX mZ μ)
    {f : Ω → E} (hfm : StronglyMeasurable[mX] f) (hfi : Integrable f μ) :
    μ[f | mY ⊔ mZ] =ᵐ[μ] μ[f | mY] := by
  have hY : mY ≤ m := hYX.trans hX
  have hsup : mY ⊔ mZ ≤ m := sup_le hY hZ
  have hgm : StronglyMeasurable[mX] (μ[f | mY]) :=
    stronglyMeasurable_condExp.mono hYX
  have hgi : Integrable (μ[f | mY]) μ := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsup hfi
    (fun _ _ _ => hgi.integrableOn) (fun s hs _ => ?_) ?_).symm
  · apply setIntegral_eq_of_fieldRectangles hY hZ hgi hfi _ s hs
    intro a b ha hb
    rw [setIntegral_inter_of_indep hX hZ hind hgm hgi (hYX a ha) hb,
      setIntegral_inter_of_indep hX hZ hind hfm hfi (hYX a ha) hb,
      setIntegral_condExp hY hfi ha]
  · exact (stronglyMeasurable_condExp.mono
      (show mY ≤ mY ⊔ mZ from le_sup_left)).aestronglyMeasurable

theorem condExp_sup_comap_of_indepFun [IsFiniteMeasure μ]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {β : Type u_3} {γ : Type u_4} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → E} {Y : Ω → β} {Z : Ω → γ}
    (hf : Measurable f) (hY : Measurable Y) (hZ : Measurable Z)
    (hfi : Integrable f μ) (hind : IndepFun (fun x => (f x, Y x)) Z μ) :
    μ[f | MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap Z inferInstance]
      =ᵐ[μ] μ[f | MeasurableSpace.comap Y inferInstance] := by
  let mXY : MeasurableSpace Ω := MeasurableSpace.comap (fun x => (f x, Y x)) inferInstance
  have hfXY : @Measurable Ω E mXY _ f :=
    measurable_fst.comp (comap_measurable _)
  have hYXY : @Measurable Ω β mXY _ Y :=
    measurable_snd.comp (comap_measurable _)
  exact condExp_sup_of_indep (hf.prodMk hY).comap_le hZ.comap_le hYXY.comap_le
    hind hfXY.stronglyMeasurable hfi

theorem posterior_of_independent_auxiliary [IsFiniteMeasure μ]
    {mX mY mZ mHistory : MeasurableSpace Ω}
    (hX : mX ≤ m) (hZ : mZ ≤ m) (hYX : mY ≤ mX)
    (hind : Indep mX mZ μ) (hHistory : mHistory = mY ⊔ mZ)
    {f posterior : Ω → E} (hfm : StronglyMeasurable[mX] f) (hfi : Integrable f μ)
    (hposterior : posterior =ᵐ[μ] μ[f | mY]) :
    posterior =ᵐ[μ] μ[f | mHistory] := by
  rw [hHistory]
  exact hposterior.trans (condExp_sup_of_indep hX hZ hYX hind hfm hfi).symm

end Problem336AdditiveD139.IndependentConditioning

end

end OAI
