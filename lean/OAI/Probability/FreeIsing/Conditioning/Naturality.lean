import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem condExp_comp_measurePreserving_equiv
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {mSmall m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : mSmall ≤ m)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (heSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv)
    (heSymmSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv.symm)
    {f : Ω → E} (hf : Integrable f μ) :
    (μ[f | mSmall]) ∘ e =ᵐ[μ] μ[f ∘ e | mSmall] := by
  have hfc : Integrable (f ∘ e) μ := he.integrable_comp_of_integrable hf
  have hgc : Integrable ((μ[f | mSmall]) ∘ e) μ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfc (fun s _ _ => hgc.integrableOn)
  · intro s hs _
    have hImage : MeasurableSet[mSmall] (e '' s) := by
      rw [e.image_eq_preimage_symm]
      exact heSymmSmall hs
    calc
      (∫ x in s, ((μ[f | mSmall]) ∘ e) x ∂μ) =
          ∫ x in e '' s, (μ[f | mSmall]) x ∂μ :=
        (he.setIntegral_image_emb e.measurableEmbedding _ _).symm
      _ = ∫ x in e '' s, f x ∂μ := setIntegral_condExp hm hf hImage
      _ = ∫ x in s, (f ∘ e) x ∂μ :=
        he.setIntegral_image_emb e.measurableEmbedding _ _
  · exact (stronglyMeasurable_condExp.comp_measurable heSmall).aestronglyMeasurable

theorem condExp_ae_invariant_of_ae_invariant
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {mSmall m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : mSmall ≤ m)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (heSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv)
    (heSymmSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv.symm)
    {f : Ω → E} (hf : Integrable f μ) (hinv : f ∘ e =ᵐ[μ] f) :
    (μ[f | mSmall]) ∘ e =ᵐ[μ] μ[f | mSmall] :=
  (condExp_comp_measurePreserving_equiv hm e he heSmall heSymmSmall hf).trans
    (condExp_congr_ae hinv)

def finiteGroupAverage
    {G Ω E : Type*} [Group G] [Fintype G] [MulAction G Ω]
    [AddCommGroup E] [Module ℝ E] (f : Ω → E) (x : Ω) : E :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, f (g • x)

theorem finiteGroupAverage_invariant
    {G Ω E : Type*} [Group G] [Fintype G] [MulAction G Ω]
    [AddCommGroup E] [Module ℝ E] (f : Ω → E) (h : G) (x : Ω) :
    finiteGroupAverage (G := G) f (h • x) = finiteGroupAverage (G := G) f x := by
  unfold finiteGroupAverage
  congr 1
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => f (g • x))

theorem stronglyMeasurable_finiteGroupAverage
    {G Ω E : Type*} [Group G] [Fintype G] [MulAction G Ω]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hact : ∀ g : G, Measurable (fun x : Ω => g • x))
    {f : Ω → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (finiteGroupAverage (G := G) f) := by
  exact (Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun g _ => hf.comp_measurable (hact g))).fun_const_smul ((Fintype.card G : ℝ)⁻¹)

theorem finiteGroupAverage_ae_eq
    {G Ω E : Type*} [Group G] [Fintype G] [MulAction G Ω]
    [MeasurableSpace Ω] [AddCommGroup E] [Module ℝ E]
    {μ : Measure Ω} {f : Ω → E}
    (hinv : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    finiteGroupAverage (G := G) f =ᵐ[μ] f := by
  have hall : ∀ᵐ x ∂μ, ∀ g : G, f (g • x) = f x := ae_all_iff.mpr hinv
  filter_upwards [hall] with x hx
  simp only [finiteGroupAverage, hx, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp

theorem exists_stronglyMeasurable_invariant_version
    {G Ω E : Type*} [Group G] [Fintype G] [MulAction G Ω]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} (hact : ∀ g : G, Measurable (fun x : Ω => g • x))
    {f : Ω → E} (hf : StronglyMeasurable f)
    (hinv : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ f' : Ω → E, StronglyMeasurable f' ∧ f' =ᵐ[μ] f ∧
      ∀ (g : G) (x : Ω), f' (g • x) = f' x :=
  ⟨finiteGroupAverage (G := G) f, stronglyMeasurable_finiteGroupAverage hact hf,
    finiteGroupAverage_ae_eq hinv, finiteGroupAverage_invariant f⟩

end Problem367

end

end OAI
