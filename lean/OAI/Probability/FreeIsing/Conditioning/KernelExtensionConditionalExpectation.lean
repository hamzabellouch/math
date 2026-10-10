import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory

namespace Problem367.KernelExtensionConditionalExpectation

variable {Ω S X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace S] [mX : MeasurableSpace X]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω}

theorem condExp_fst_compProd
    (hm : m ≤ mΩ) {p : Ω → S} (hp : Measurable[m] p)
    (κ : Kernel S X) [IsMarkovKernel κ] {f : Ω → ℝ} (hf : Integrable f μ) :
    let ρ := μ ⊗ₘ κ.comap p (hp.mono hm le_rfl)
    ρ[(fun z : Ω × X => f z.1) | m.prod mX] =ᵐ[ρ]
      fun z => μ[f | m] z.1 := by
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Ω × X) := mΩ.prod mX
  let k := κ.comap p (hp.mono hm le_rfl)
  let ρ := μ ⊗ₘ k
  have hfst : @MeasurePreserving (Ω × X) Ω (mΩ.prod mX) mΩ Prod.fst ρ μ :=
    ⟨measurable_fst, Measure.fst_compProd μ k⟩
  have hF : Integrable (fun z : Ω × X => f z.1) ρ :=
    hfst.integrable_comp_of_integrable hf
  have hG : Integrable (fun z : Ω × X => μ[f | m] z.1) ρ :=
    hfst.integrable_comp_of_integrable integrable_condExp
  have hsmall : m.prod mX ≤ mΩ.prod mX :=
    sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  have hsm : StronglyMeasurable[m.prod mX]
      (fun z : Ω × X => μ[f | m] z.1) :=
    stronglyMeasurable_condExp.comp_measurable measurable_fst
  have hrect (a : Set Ω) (ha : MeasurableSet[m] a)
      (b : Set X) (hb : MeasurableSet b) :
      (∫ z in a ×ˢ b, μ[f | m] z.1 ∂ρ) = ∫ z in a ×ˢ b, f z.1 ∂ρ := by
    let w : Ω → ℝ := fun ω => (κ (p ω)).real b
    have hw : StronglyMeasurable[m] w :=
      ((κ.measurable_coe hb).ennreal_toReal.comp hp).stronglyMeasurable
    have hwb : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ (1 : ℝ) := by
      apply Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    have hwf : Integrable (w * f) μ :=
      hf.bdd_mul (hw.mono hm).aestronglyMeasurable hwb
    have he : μ[w * f | m] =ᵐ[μ] w * μ[f | m] :=
      condExp_stronglyMeasurable_mul_of_bound hm hw hf 1 hwb
    rw [Measure.setIntegral_compProd (hm a ha) hb hG.integrableOn,
      Measure.setIntegral_compProd (hm a ha) hb hF.integrableOn]
    simp only [setIntegral_const, smul_eq_mul]
    change (∫ ω in a, w ω * μ[f | m] ω ∂μ) = ∫ ω in a, w ω * f ω ∂μ
    calc
      _ = ∫ ω in a, μ[w * f | m] ω ∂μ :=
        setIntegral_congr_ae (hm a ha) (he.symm.mono (fun ω hω _ => hω))
      _ = _ := setIntegral_condExp hm hwf ha
  have hwhole : (∫ z, μ[f | m] z.1 ∂ρ) = ∫ z : Ω × X, f z.1 ∂ρ := by
    simpa only [univ_prod_univ, Measure.restrict_univ] using
      hrect univ MeasurableSet.univ univ MeasurableSet.univ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsmall hF
    (fun a _ _ => hG.integrableOn) ?_ hsm.aestronglyMeasurable).symm
  intro a ha _
  refine MeasurableSpace.induction_on_inter
    (@generateFrom_prod Ω X m mX).symm (@isPiSystem_prod Ω X m mX)
    (by simp) ?_ ?_ ?_ a ha
  · rintro u ⟨s, hs, t, ht, rfl⟩
    exact hrect s hs t ht
  · intro a ha he
    rw [setIntegral_compl (hsmall a ha) hG,
      setIntegral_compl (hsmall a ha) hF, hwhole, he]
  · intro a hdisj ha he
    rw [integral_iUnion (fun i => hsmall _ (ha i)) hdisj hG.integrableOn,
      integral_iUnion (fun i => hsmall _ (ha i)) hdisj hF.integrableOn]
    exact tsum_congr he

end Problem367.KernelExtensionConditionalExpectation

end

end OAI
