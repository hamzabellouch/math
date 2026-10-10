import Mathlib
import OAI.Probability.LogConcave.Dynamics.Squared

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d : ℕ}

lemma norm_sub_sq_three (x y z : Point d) : ‖x-z‖^2≤2*‖x-y‖^2+2*‖y-z‖^2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub x y z
  nlinarith [sq_nonneg (‖x-y‖-‖y-z‖),norm_nonneg (x-z),norm_nonneg (x-y),norm_nonneg (y-z)]

theorem SquaredAt.trans [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} {ν : Measure Γ} {θ : Measure W} {f : Ω → Point d}
    {g : Γ → Point d} {h : W → Point d} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {B C : ℝ} (h₁ : SquaredAt μ ν f g B) (h₂ : SquaredAt ν θ g h C) :
    SquaredAt μ θ f h (2*B+2*C) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h₁
  obtain ⟨ι,hι,hll,hrr,hii,hee⟩ := h₂
  let := hκ
  let := hι
  have hlink : κ.map Prod.snd=ι.fst := hr.trans hll.symm
  let Λ := lift κ ι Prod.snd measurable_snd
  have hp : Λ.fst=κ := lift_fst κ ι Prod.snd measurable_snd
  have hm : Λ.map (fun z => (z.1.2,z.2))=ι := lift_map κ ι Prod.snd measurable_snd hlink
  have hi₁ : Integrable (fun z : (Ω × Γ) × W => ‖f z.1.1-g z.1.2‖^2) Λ := by
    have hk : Integrable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) (Λ.map Prod.fst) := by
      change Integrable _ Λ.fst
      rw [hp]
      exact hi
    exact hk.comp_measurable measurable_fst
  have E₁ : (∫z,‖f z.1.1-g z.1.2‖^2 ∂Λ)≤B := by
    have hm₁ : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
    rw [←integral_map measurable_fst.aemeasurable hm₁.aestronglyMeasurable]
    change (∫z,‖f z.1-g z.2‖^2 ∂Λ.fst)≤B
    rw [hp]
    exact he
  have H₂ := lift_integrable κ ι Prod.snd measurable_snd hlink _ hii
  have hi₂ : Integrable (fun z : (Ω × Γ) × W => ‖g z.1.2-h z.2‖^2) Λ := H₂.1
  have E₂ : (∫z,‖g z.1.2-h z.2‖^2 ∂Λ)≤C := H₂.2.trans_le hee
  have hdom := (hi₁.const_mul 2).add (hi₂.const_mul 2)
  have hb (z : (Ω × Γ) × W) : ‖f z.1.1-h z.2‖^2≤
      2*‖f z.1.1-g z.1.2‖^2+2*‖g z.1.2-h z.2‖^2 := norm_sub_sq_three _ _ _
  have hcost : Measurable (fun z : (Ω × Γ) × W => ‖f z.1.1-h z.2‖^2) := by fun_prop
  have hnew := hdom.mono' hcost.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using hb z)
  refine SquaredAt.of_joint Λ μ θ (fun z => z.1.1) Prod.snd (by fun_prop) measurable_snd
    ?_ ?_ f h hf hh hnew ?_
  · change Measure.map (Prod.fst ∘ Prod.fst) Λ=μ
    rw [←Measure.map_map measurable_fst measurable_fst]
    change Λ.fst.map Prod.fst=μ
    rw [hp]
    exact hl
  · have hs := congrArg (Measure.map Prod.snd) hm
    rw [Measure.map_map measurable_snd (by fun_prop)] at hs
    exact hs.trans hrr
  · apply (integral_mono hnew hdom hb).trans
    simp only [Pi.add_apply]
    rw [integral_add (hi₁.const_mul 2) (hi₂.const_mul 2),integral_const_mul,integral_const_mul]
    linarith

lemma SquaredAt.same_tape (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → Point d) (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hi : Integrable (fun z => ‖f z-g z‖^2) μ) (he : (∫z,‖f z-g z‖^2 ∂μ)≤B) :
    SquaredAt μ μ f g B :=
  SquaredAt.of_joint μ μ μ id id measurable_id measurable_id (Measure.map_id) (Measure.map_id)
    f g hf hg hi he
end LogConcaveSampling.Coupling

end

end

end OAI
