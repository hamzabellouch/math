import OAI.InformationTheory.Entanglement.TranscriptLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped MeasureTheory ProbabilityTheory Topology
namespace SecretKey
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma setIntegral_eq_on_generated {μ : Measure Ω} {F : MeasurableSpace Ω}
    (hF : F ≤ mΩ) {p : Set (Set Ω)} (hp : IsPiSystem p)
    (hgen : F=MeasurableSpace.generateFrom p) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (huniv : (∫ x, f x ∂μ)=(∫ x, g x ∂μ))
    (hbasic : ∀ s∈p, (∫ x in s, f x ∂μ)=(∫ x in s, g x ∂μ)) :
    ∀ s, MeasurableSet[F] s → (∫ x in s, f x ∂μ)=(∫ x in s, g x ∂μ) := by
  apply @MeasurableSpace.induction_on_inter Ω F
    (fun s _ => (∫ x in s, f x ∂μ)=(∫ x in s, g x ∂μ)) p hgen hp
  · simp
  · exact hbasic
  · intro s hs heq
    have ha := integral_add_compl (hF s hs) hf
    have hb := integral_add_compl (hF s hs) hg
    linarith
  · intro s hd hs heq
    rw [integral_iUnion (fun i => hF _ (hs i)) hd hf.integrableOn,
      integral_iUnion (fun i => hF _ (hs i)) hd hg.integrableOn]
    exact tsum_congr heq

def joinTests (A F : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a t, MeasurableSet[A] a ∧ MeasurableSet[F] t ∧ s=a∩t}
lemma joinTests_pi (A F : MeasurableSpace Ω) : IsPiSystem (joinTests A F) := by
  rintro s ⟨a,t,ha,ht,rfl⟩ u ⟨b,v,hb,hv,rfl⟩ _
  refine ⟨a∩b,t∩v,ha.inter hb,ht.inter hv,?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto
lemma joinTests_generate (A F : MeasurableSpace Ω) :
    A ⊔ F=MeasurableSpace.generateFrom (joinTests A F) := by
  apply le_antisymm
  · apply sup_le
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨s,Set.univ,hs,MeasurableSet.univ,(Set.inter_univ s).symm⟩
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ,s,MeasurableSet.univ,hs,(Set.univ_inter s).symm⟩
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨a,t,ha,ht,rfl⟩
    exact ((le_sup_left : A ≤ A ⊔ F) _ ha).inter ((le_sup_right : F ≤ A ⊔ F) _ ht)

variable [standardBorel : StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {F A B : MeasurableSpace Ω} (hF : F ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
lemma indicator_one_mul (s : Set Ω) (f : Ω → ℝ) : s.indicator 1*f=s.indicator f := by
  ext x
  by_cases hx : x∈s <;> simp [hx]
omit standardBorel in
lemma integrable_indicator_one (s : Set Ω) (hs : MeasurableSet[mΩ] s) :
    Integrable (s.indicator (1 : Ω → ℝ)) μ := (integrable_const _).indicator hs
include hA hB in

theorem conditional_marginal_join (hind : CondIndep F A B hF μ)
    {b : Set Ω} (hb : MeasurableSet[B] b) :
    (μ⟦b | F⟧) =ᵐ[μ] (μ⟦b | A ⊔ F⟧) := by
  have hAF : A ⊔ F ≤ mΩ := sup_le hA hF
  have hbi := integrable_indicator_one (μ := μ) b (hB b hb)
  apply ae_eq_condExp_of_forall_setIntegral_eq hAF hbi
  · intro s hs _
    exact integrable_condExp.integrableOn
  · intro s hs _
    apply setIntegral_eq_on_generated hAF (joinTests_pi A F) (joinTests_generate A F)
      integrable_condExp hbi (integral_condExp hF) _ s hs
    rintro u ⟨a,t,ha,ht,rfl⟩
    have hai := integrable_indicator_one (μ := μ) a (hA a ha)
    have hprod : Integrable (a.indicator (1 : Ω → ℝ) * (μ⟦b | F⟧)) μ := by
      rw [indicator_one_mul]
      exact integrable_condExp.indicator (hA a ha)
    have he := condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_condExp (m := F)) hprod hai
    have hi := (condIndep_iff F A B hF hA hB μ).mp hind a b ha hb
    have heq : μ[a.indicator (1 : Ω → ℝ) * (μ⟦b | F⟧) | F] =ᵐ[μ] (μ⟦a∩b | F⟧) := he.trans hi.symm
    have hh := setIntegral_congr_ae (hF t ht) (heq.mono (fun x hx _ => hx))
    have habi : Integrable ((a∩b).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const _).indicator ((hA a ha).inter (hB b hb))
    rw [setIntegral_condExp hF hprod ht,setIntegral_condExp hF habi ht] at hh
    change (∫ x in t, (a.indicator (1 : Ω → ℝ) * (μ⟦b | F⟧)) x ∂μ)=
      (∫ x in t, (a∩b).indicator (1 : Ω → ℝ) x ∂μ) at hh
    rw [indicator_one_mul,setIntegral_indicator (hA a ha)] at hh
    rw [show (a∩b).indicator (1 : Ω → ℝ)=a.indicator (b.indicator (1 : Ω → ℝ)) by
      ext x; by_cases hxa : x∈a <;> by_cases hxb : x∈b <;> simp [hxa,hxb],
      setIntegral_indicator (hA a ha)] at hh
    simpa only [Set.inter_comm t a, Pi.one_def] using hh
  · exact (stronglyMeasurable_condExp (m := F) (μ := μ) (f := b.indicator (fun _ => (1 : ℝ)))).mono
      (show F ≤ A ⊔ F from le_sup_right) |>.aestronglyMeasurable

omit standardBorel in
lemma conditional_inter_pullout {H : MeasurableSpace Ω} (hH : H ≤ mΩ)
    {a b : Set Ω} (ha : MeasurableSet[H] a) (hb : MeasurableSet[mΩ] b) :
    (μ⟦a∩b | H⟧) =ᵐ[μ] a.indicator (1 : Ω → ℝ) * (μ⟦b | H⟧) := by
  change μ[(a∩b).indicator (1 : Ω → ℝ) | H] =ᵐ[μ] _
  rw [Set.inter_indicator_one]
  apply condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_const.indicator ha)
  · change Integrable (a.indicator (1 : Ω → ℝ) * b.indicator (1 : Ω → ℝ)) μ
    rw [← Set.inter_indicator_one]
    exact integrable_indicator_one (a∩b) ((hH a ha).inter hb)
  · exact integrable_indicator_one b hb

lemma independence_of_local_marginals {D H : MeasurableSpace Ω}
    (hD : D ≤ mΩ) (hH : H ≤ mΩ) (hAH : A ≤ H) (hDH : D ≤ H)
    (hB : B ≤ mΩ)
    (hmar : ∀ b, MeasurableSet[B] b → (μ⟦b | H⟧)=ᵐ[μ](μ⟦b | D⟧)) :
    CondIndep D A B hD μ := by
  rw [condIndep_iff D A B hD (hAH.trans hH) hB μ]
  intro a b ha hb
  have hb' := hB b hb
  have hai := integrable_indicator_one (μ := μ) a (hH a (hAH a ha))
  have he0 := conditional_inter_pullout (μ := μ) hH (hAH a ha) hb'
  have he1 : (μ⟦a∩b | H⟧)=ᵐ[μ] a.indicator (1 : Ω → ℝ)*(μ⟦b | D⟧) :=
    he0.trans (Filter.EventuallyEq.rfl.mul (hmar b hb))
  have he2 := (condExp_condExp_of_le (μ := μ) (f := (a∩b).indicator (fun _ =>(1 : ℝ))) hDH hH).symm.trans
    (condExp_congr_ae (m := D) he1)
  have hp : Integrable (a.indicator (1 : Ω → ℝ) * (μ⟦b | D⟧)) μ := by
    rw [indicator_one_mul]
    exact integrable_condExp.indicator (hH a (hAH a ha))
  exact he2.trans (condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp hp hai)

include hA hB in

theorem sender_message_preserves_independence (hind : CondIndep F A B hF μ)
    {D : MeasurableSpace Ω} (hFD : F ≤ D) (hDA : D ≤ A ⊔ F) :
    CondIndep D A B (hDA.trans (sup_le hA hF)) μ := by
  have hAF : A ⊔ F ≤ mΩ := sup_le hA hF
  have hD : D ≤ mΩ := hDA.trans hAF
  apply independence_of_local_marginals hD hAF le_sup_left hDA hB
  intro b hb
  have he := conditional_marginal_join hF hA hB hind hb
  have hm : StronglyMeasurable[D] (μ⟦b | F⟧) :=
    stronglyMeasurable_condExp.mono hFD
  have he' := condExp_congr_ae (m := D) he
  rw [condExp_of_stronglyMeasurable hD hm integrable_condExp] at he'
  exact he.symm.trans (he'.trans (condExp_condExp_of_le hDA hAF))

include hA hB in

theorem public_source_preserves_independence (hind : CondIndep F A B hF μ)
    {C : MeasurableSpace Ω} (hC : C ≤ mΩ)
    (hsource : CondIndep F C (A ⊔ B) hF μ) :
    CondIndep (C ⊔ F) A B (sup_le hC hF) μ := by
  rw [condIndep_iff (C ⊔ F) A B (sup_le hC hF) hA hB μ]
  intro a b ha hb
  have hj := conditional_marginal_join hF hC (sup_le hA hB) hsource
    (((le_sup_left : A ≤ A ⊔ B) _ ha).inter ((le_sup_right : B ≤ A ⊔ B) _ hb))
  have hma := conditional_marginal_join hF hC (sup_le hA hB) hsource
    ((le_sup_left : A ≤ A ⊔ B) _ ha)
  have hmb := conditional_marginal_join hF hC (sup_le hA hB) hsource
    ((le_sup_right : B ≤ A ⊔ B) _ hb)
  exact hj.symm.trans (((condIndep_iff F A B hF hA hB μ).mp hind a b ha hb).trans
    (hma.mul hmb))
include hA hB in

theorem conditional_independence_adjoin_public (hind : CondIndep F A B hF μ) :
    CondIndep F (A ⊔ F) (B ⊔ F) hF μ := by
  have hleft : CondIndep F (A ⊔ F) B hF μ := by
    apply independence_of_local_marginals hF (sup_le hA hF) le_rfl le_sup_right hB
    intro b hb
    exact (conditional_marginal_join hF hA hB hind hb).symm
  apply CondIndep.symm
  apply independence_of_local_marginals hF (sup_le hB hF) le_rfl le_sup_right (sup_le hA hF)
  intro a ha
  exact (conditional_marginal_join hF hB (sup_le hA hF) hleft.symm ha).symm

lemma independent_of_public_conditional_laws {H : MeasurableSpace Ω}
    (hH : H ≤ mΩ) (hFH : F ≤ H) (hAH : A ≤ H) (hB : B ≤ mΩ)
    (hkernel : ∀ b, MeasurableSet[B] b → AEStronglyMeasurable[F] (μ⟦b | H⟧) μ) :
    CondIndep F A B hF μ := by
  apply independence_of_local_marginals hF hH hAH hFH hB
  intro b hb
  exact (condExp_of_aestronglyMeasurable' hF (hkernel b hb) integrable_condExp).symm.trans
    (condExp_condExp_of_le hFH hH)

end SecretKey

end

end OAI
