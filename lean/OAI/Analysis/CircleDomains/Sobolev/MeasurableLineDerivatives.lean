import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! On an open set, almost everywhere line differentiability of a measurable
function makes its line derivative measurable. The proof uses actual
difference quotients of the zero extension, so no continuity across the
exceptional lines is required. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddRightInvariant μ]

theorem aestronglyMeasurable_lineDeriv_of_ae_lineDifferentiable
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (v : E)
    (hf : AEStronglyMeasurable f (μ.restrict U))
    (hd : ∀ᵐ x ∂μ.restrict U, LineDifferentiableAt ℝ f x v) :
    AEStronglyMeasurable (fun x => lineDeriv ℝ f x v) (μ.restrict U) := by
  let F : E → ℝ := U.indicator f
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → E → ℝ := fun n x => (h n)⁻¹ * (F (x + h n • v) - F x)
  have hF : AEStronglyMeasurable F μ :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).2 hf
  have hq (n : ℕ) : AEStronglyMeasurable (q n) (μ.restrict U) := by
    have ht : AEStronglyMeasurable (fun x => F (x + h n • v)) μ :=
      hF.comp_quasiMeasurePreserving
        (measurePreserving_add_right μ (h n • v)).quasiMeasurePreserving
    exact ((ht.sub hF).const_mul (h n)⁻¹).mono_measure Measure.restrict_le_self
  have hh : Tendsto h atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hhne : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall (fun n => by
      change 1 / ((n : ℝ) + 1) ≠ 0
      positivity)⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop hq
  filter_upwards [hd, ae_restrict_mem hU.measurableSet] with x hdx hx
  have hlim := hdx.hasDerivAt.tendsto_slope_zero.comp hhne
  have hin : ∀ᶠ n in atTop, x + h n • v ∈ U := by
    have ht : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hh.smul_const v)
    exact ht (hU.mem_nhds hx)
  apply hlim.congr'
  filter_upwards [hin] with n hn
  simp [q, F, indicator_of_mem hn, indicator_of_mem hx, smul_eq_mul]

/-- A Borel representative agrees with the line derivative at every
differentiability point outside one fixed null set. This implication form
can be sliced by Fubini before asserting almost everywhere differentiability. -/
theorem exists_measurable_lineDeriv_representative
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (v : E)
    (hf : AEStronglyMeasurable f (μ.restrict U)) :
    ∃ G : E → ℝ, Measurable G ∧
      ∀ᵐ x ∂μ, x ∈ U → LineDifferentiableAt ℝ f x v →
        G x = lineDeriv ℝ f x v := by
  let F : E → ℝ := U.indicator f
  have hF : AEStronglyMeasurable F μ :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).2 hf
  let F₀ := hF.mk F
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → E → ℝ := fun n x => (h n)⁻¹ * (F₀ (x + h n • v) - F₀ x)
  have hq (n : ℕ) : Measurable (q n) :=
    ((hF.measurable_mk.comp (continuous_id.add continuous_const).measurable).sub
      hF.measurable_mk).const_mul _
  refine ⟨fun x => limsup (fun n => q n x) atTop, Measurable.limsup hq, ?_⟩
  have he (n : ℕ) : ∀ᵐ x ∂μ, F (x + h n • v) = F₀ (x + h n • v) :=
    (measurePreserving_add_right μ (h n • v)).quasiMeasurePreserving.ae hF.ae_eq_mk
  filter_upwards [hF.ae_eq_mk, ae_all_iff.2 he] with x hx₀ hx₁ hx hd
  have hx₀' : F x = F₀ x := hx₀
  have hh : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by
        change 1 / ((n : ℝ) + 1) ≠ 0
        positivity)⟩
  have hlim := hd.hasDerivAt.tendsto_slope_zero.comp hh
  have hin : ∀ᶠ n in atTop, x + h n • v ∈ U := by
    have ht : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add ((tendsto_nhds_of_tendsto_nhdsWithin hh).smul_const v)
    exact ht (hU.mem_nhds hx)
  have hq_lim : Tendsto (fun n => q n x) atTop (𝓝 (lineDeriv ℝ f x v)) := by
    apply hlim.congr'
    filter_upwards [hin] with n hn
    simp only [q, ← hx₀', ← hx₁ n, F, indicator_of_mem hn,
      indicator_of_mem hx, zero_add, zero_smul, add_zero, smul_eq_mul, Function.comp_apply]
  exact hq_lim.limsup_eq

end CircleDomainRigidity

end

end OAI
