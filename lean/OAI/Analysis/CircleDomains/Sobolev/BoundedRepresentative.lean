import OAI.Analysis.CircleDomains.Sobolev.PositiveLocalAverages
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace OAI

/-! A bounded measurable representative can be chosen without changing
any completed-measure class, and used in every absolutely continuous
sampling measure. -/

open Set Filter MeasureTheory

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem exists_measurable_unit_representative
    (μ : Measure X) (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ x ∂μ, u x ∈ Icc 0 1) :
    ∃v : X → ℝ, Measurable v ∧ (∀x, v x ∈ Icc 0 1) ∧ u =ᵐ[μ] v := by
  let v : X → ℝ := fun x => max 0 (min 1 (hu.mk u x))
  refine ⟨v, measurable_const.max (measurable_const.min hu.measurable_mk), ?_, ?_⟩
  · intro x
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · filter_upwards [hu.ae_eq_mk, hb] with x hx hbx
    change u x = max 0 (min 1 (hu.mk u x))
    rw [← hx, min_eq_right hbx.2, max_eq_right hbx.1]

theorem integral_representative_eq
    (μ ν : Measure X) (hν : ν ≪ μ) {u v : X → ℝ} (h : u =ᵐ[μ] v) :
    (∫x, u x ∂ν) = ∫x, v x ∂ν := integral_congr_ae (hν.ae_le h)

end CircleDomainRigidity

end

end OAI
