import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}

theorem integral_sq_sub_copies_eq_two_variance (hX : MemLp X 2 μ) :
    (∫ p : Ω × Ω, (X p.1 - X p.2) ^ 2 ∂μ.prod μ) =
      2 * variance X μ := by
  have h₁ : MemLp (fun p : Ω × Ω => X p.1) 2 (μ.prod μ) := hX.comp_fst μ
  have h₂ : MemLp (fun p : Ω × Ω => X p.2) 2 (μ.prod μ) := hX.comp_snd μ
  have hm : (∫ p : Ω × Ω, (X p.1 - X p.2) ∂μ.prod μ) = 0 := by
    rw [integral_sub (h₁.integrable (by simp)) (h₂.integrable (by simp))]
    simp [integral_fun_fst, integral_fun_snd]
  have hv := variance_of_integral_eq_zero
    (X := fun p : Ω × Ω => X p.1 - X p.2) (h₁.sub h₂).aemeasurable hm
  rw [← hv]
  rw [variance_fun_sub h₁ h₂, covariance_fst_snd_prod hX hX,
    measurePreserving_fst.variance_fun_comp hX.aemeasurable,
    measurePreserving_snd.variance_fun_comp hX.aemeasurable]
  ring

theorem integral_sq_sub_copies (hX : MemLp X 2 μ) :
    (∫ p : Ω × Ω, (X p.1 - X p.2) ^ 2 ∂μ.prod μ) =
      2 * ((∫ x, X x ^ 2 ∂μ) - (∫ x, X x ∂μ) ^ 2) := by
  rw [integral_sq_sub_copies_eq_two_variance hX, variance_eq_sub hX]
  rfl

theorem ae_eq_integral_of_copies_ae_eq (hX : MemLp X 2 μ)
    (hcopy : ∀ᵐ p : Ω × Ω ∂μ.prod μ, X p.1 = X p.2) :
    ∀ᵐ x ∂μ, X x = ∫ y, X y ∂μ := by
  apply ae_eq_integral_of_variance_eq_zero hX
  have hz : (∫ p : Ω × Ω, (X p.1 - X p.2) ^ 2 ∂μ.prod μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hcopy] with p hp
    simp [hp]
  rw [integral_sq_sub_copies_eq_two_variance hX] at hz
  linarith

section Kernel

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [SFinite ν]
    {κ : Kernel W Ω} [IsMarkovKernel κ]

theorem ae_memLp_two_of_compProd {Y : W × Ω → ℝ}
    (hY : MemLp Y 2 (ν ⊗ₘ κ)) :
    ∀ᵐ w ∂ν, MemLp (fun x => Y (w, x)) 2 (κ w) := by
  have hm : ∀ᵐ w ∂ν, AEStronglyMeasurable (fun x => Y (w, x)) (κ w) :=
    AEStronglyMeasurable.ae_of_compProd (f := fun w x => Y (w, x))
      (by
        convert hY.aestronglyMeasurable using 1
        funext p
        cases p
        rfl)
  have hi : ∀ᵐ w ∂ν, Integrable (fun x => Y (w, x) ^ 2) (κ w) :=
    ((Measure.integrable_compProd_iff hY.integrable_sq.aestronglyMeasurable).1
      hY.integrable_sq).1
  filter_upwards [hm, hi] with w hmw hiw
  exact (memLp_two_iff_integrable_sq hmw).2 hiw

theorem exists_measurable_recovery_of_copies_ae_eq (hXm : Measurable X)
    (hX : ∀ᵐ w ∂ν, MemLp X 2 (κ w))
    (hcopy : ∀ᵐ z : W × (Ω × Ω) ∂ν ⊗ₘ (κ ×ₖ κ), X z.2.1 = X z.2.2) :
    ∃ F : W → ℝ, Measurable F ∧
      ∀ᵐ z : W × Ω ∂ν ⊗ₘ κ, X z.2 = F z.1 := by
  let F : W → ℝ := fun w => ∫ x, X x ∂κ w
  have hF : Measurable F := hXm.stronglyMeasurable.integral_kernel.measurable
  refine ⟨F, hF, ?_⟩
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (hXm.comp measurable_snd) (hF.comp measurable_fst))
  have hc := Measure.ae_ae_of_ae_compProd hcopy
  filter_upwards [hX, hc] with w hw hcw
  apply ae_eq_integral_of_copies_ae_eq hw
  simpa [Kernel.prod_apply] using hcw

theorem exists_measurable_recovery_of_memLp_copies_ae_eq (hXm : Measurable X)
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ))
    (hcopy : ∀ᵐ z : W × (Ω × Ω) ∂ν ⊗ₘ (κ ×ₖ κ), X z.2.1 = X z.2.2) :
    ∃ F : W → ℝ, Measurable F ∧
      ∀ᵐ z : W × Ω ∂ν ⊗ₘ κ, X z.2 = F z.1 :=
  exists_measurable_recovery_of_copies_ae_eq hXm (ae_memLp_two_of_compProd hX) hcopy

theorem exists_measurable_recovery_array_of_copies_ae_eq
    {ι : Type*} [Countable ι] (Y : ι → Ω → ℝ)
    (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, ∀ᵐ w ∂ν, MemLp (Y i) 2 (κ w))
    (hcopy : ∀ᵐ z : W × (Ω × Ω) ∂ν ⊗ₘ (κ ×ₖ κ),
      ∀ i, Y i z.2.1 = Y i z.2.2) :
    ∃ F : W → (ι → ℝ), Measurable F ∧
      ∀ᵐ z : W × Ω ∂ν ⊗ₘ κ, ∀ i, Y i z.2 = F z.1 i := by
  have hi : ∀ i, ∃ F : W → ℝ, Measurable F ∧
      ∀ᵐ z : W × Ω ∂ν ⊗ₘ κ, Y i z.2 = F z.1 := by
    intro i
    apply exists_measurable_recovery_of_copies_ae_eq (hYm i) (hY i)
    filter_upwards [hcopy] with z hz using hz i
  choose F hFm hF using hi
  refine ⟨fun w i => F i w, Measurable.of_eval hFm, ?_⟩
  exact ae_all_iff.2 hF

end Kernel

end Problem367

end

end OAI
