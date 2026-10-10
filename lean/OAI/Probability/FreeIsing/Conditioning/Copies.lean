import OAI.Probability.FreeIsing.Conditioning.CopyVariance
import OAI.Probability.FreeIsing.Conditioning.KernelConditionalExpectation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    (ν : Measure W) [SFinite ν] (κ : Kernel W Ω) [IsMarkovKernel κ]

theorem measurePreserving_conditionalCopy_fst :
    MeasurePreserving (Prod.map id Prod.fst : W × (Ω × Ω) → W × Ω)
      (ν ⊗ₘ (κ ×ₖ κ)) (ν ⊗ₘ κ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]

theorem measurePreserving_conditionalCopy_snd :
    MeasurePreserving (Prod.map id Prod.snd : W × (Ω × Ω) → W × Ω)
      (ν ⊗ₘ (κ ×ₖ κ)) (ν ⊗ₘ κ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_map measurable_snd, ← Kernel.snd_eq, Kernel.snd_prod]

variable {ν κ}

theorem memLp_conditionalCopy_fst {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    MemLp (fun z : W × (Ω × Ω) => X z.2.1) 2 (ν ⊗ₘ (κ ×ₖ κ)) := by
  convert hX.comp_measurePreserving (measurePreserving_conditionalCopy_fst ν κ) using 1
  rfl

theorem memLp_conditionalCopy_snd {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    MemLp (fun z : W × (Ω × Ω) => X z.2.2) 2 (ν ⊗ₘ (κ ×ₖ κ)) := by
  convert hX.comp_measurePreserving (measurePreserving_conditionalCopy_snd ν κ) using 1
  rfl

theorem ae_memLp_conditionalCopies_fiber {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    ∀ᵐ z : W × (Ω × Ω) ∂ν ⊗ₘ (κ ×ₖ κ), MemLp X 2 (κ z.1) := by
  refine ae_of_ae_map (μ := ν ⊗ₘ (κ ×ₖ κ)) (f := Prod.fst)
    (p := fun w => MemLp X 2 (κ w)) measurable_fst.aemeasurable ?_
  change ∀ᵐ w ∂(ν ⊗ₘ (κ ×ₖ κ)).fst, MemLp X 2 (κ w)
  rw [Measure.fst_compProd]
  exact ae_memLp_two_of_compProd hX

theorem integral_sq_sub_conditionalCopies {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    (∫ z : W × (Ω × Ω), (X z.2.1 - X z.2.2) ^ 2 ∂ν ⊗ₘ (κ ×ₖ κ)) =
      2 * ∫ w, variance X (κ w) ∂ν := by
  have h₁ := memLp_conditionalCopy_fst hX
  have h₂ := memLp_conditionalCopy_snd hX
  have hi : Integrable (fun z : W × (Ω × Ω) => (X z.2.1 - X z.2.2) ^ 2)
      (ν ⊗ₘ (κ ×ₖ κ)) := (h₁.sub h₂).integrable_sq
  rw [Measure.integral_compProd hi]
  calc
    (∫ w, ∫ p : Ω × Ω, (X p.1 - X p.2) ^ 2 ∂(κ ×ₖ κ) w ∂ν) =
        ∫ w, 2 * variance X (κ w) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_memLp_two_of_compProd hX] with w hw
      simpa only [Kernel.prod_apply] using integral_sq_sub_copies_eq_two_variance hw
    _ = 2 * ∫ w, variance X (κ w) ∂ν := integral_const_mul _ _

theorem integrable_variance_kernel {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    Integrable (fun w => variance X (κ w)) ν := by
  have hi : Integrable (fun z : W × (Ω × Ω) => (X z.2.1 - X z.2.2) ^ 2)
      (ν ⊗ₘ (κ ×ₖ κ)) :=
    ((memLp_conditionalCopy_fst hX).sub (memLp_conditionalCopy_snd hX)).integrable_sq
  have hn := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).1 hi).2
  have hm : Integrable (fun w => ∫ p : Ω × Ω,
      (X p.1 - X p.2) ^ 2 ∂(κ ×ₖ κ) w) ν := by
    simpa only [Real.norm_eq_abs, abs_sq] using hn
  have hv : Integrable (fun w => 2 * variance X (κ w)) ν := hm.congr (by
    filter_upwards [ae_memLp_two_of_compProd hX] with w hw
    simpa only [Kernel.prod_apply] using integral_sq_sub_copies_eq_two_variance hw)
  convert hv.const_mul (1 / 2 : ℝ) using 1
  funext w
  ring

theorem conditionalCopies_ae_eq_of_integral_variance_eq_zero {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ))
    (hv : (∫ w, variance X (κ w) ∂ν) = 0) :
    ∀ᵐ z : W × (Ω × Ω) ∂ν ⊗ₘ (κ ×ₖ κ), X z.2.1 = X z.2.2 := by
  have hi : Integrable (fun z : W × (Ω × Ω) => (X z.2.1 - X z.2.2) ^ 2)
      (ν ⊗ₘ (κ ×ₖ κ)) :=
    ((memLp_conditionalCopy_fst hX).sub (memLp_conditionalCopy_snd hX)).integrable_sq
  have hz : (∫ z : W × (Ω × Ω), (X z.2.1 - X z.2.2) ^ 2
      ∂ν ⊗ₘ (κ ×ₖ κ)) = 0 := by
    rw [integral_sq_sub_conditionalCopies hX, hv, mul_zero]
  have heq := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).1 hz
  filter_upwards [heq] with z hz
  simpa only [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero] using hz

section ConditionalExpectation

variable [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure ν]

theorem condExp_sq_sub_conditionalCopies {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    (ν ⊗ₘ (κ ×ₖ κ))[(fun z : W × (Ω × Ω) => (X z.2.1 - X z.2.2) ^ 2) |
        (inferInstance : MeasurableSpace W).comap Prod.fst] =ᵐ[ν ⊗ₘ (κ ×ₖ κ)]
      fun z => 2 * variance X (κ z.1) := by
  have hi : Integrable (fun z : W × (Ω × Ω) => (X z.2.1 - X z.2.2) ^ 2)
      (ν ⊗ₘ (κ ×ₖ κ)) :=
    ((memLp_conditionalCopy_fst hX).sub (memLp_conditionalCopy_snd hX)).integrable_sq
  have hlift := ae_memLp_conditionalCopies_fiber hX
  filter_upwards [condExp_compProd_fst hi, hlift] with z hcz hz
  rw [hcz, Kernel.prod_apply]
  exact integral_sq_sub_copies_eq_two_variance hz

theorem condExp_sub_conditionalCopies {X : Ω → ℝ}
    (hX : MemLp (fun z : W × Ω => X z.2) 2 (ν ⊗ₘ κ)) :
    (ν ⊗ₘ (κ ×ₖ κ))[(fun z : W × (Ω × Ω) => X z.2.1 - X z.2.2) |
        (inferInstance : MeasurableSpace W).comap Prod.fst] =ᵐ[ν ⊗ₘ (κ ×ₖ κ)] 0 := by
  have hi : Integrable (fun z : W × (Ω × Ω) => X z.2.1 - X z.2.2)
      (ν ⊗ₘ (κ ×ₖ κ)) :=
    ((memLp_conditionalCopy_fst hX).sub (memLp_conditionalCopy_snd hX)).integrable (by simp)
  filter_upwards [condExp_compProd_fst hi, ae_memLp_conditionalCopies_fiber hX]
    with z hcz hz
  rw [hcz, Kernel.prod_apply,
    integral_sub ((hz.comp_fst (κ z.1)).integrable (by simp))
      ((hz.comp_snd (κ z.1)).integrable (by simp))]
  simp [integral_fun_fst, integral_fun_snd]

end ConditionalExpectation

end Problem367

end

end OAI
