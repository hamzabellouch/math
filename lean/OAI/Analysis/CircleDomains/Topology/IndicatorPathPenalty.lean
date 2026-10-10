import OAI.Analysis.CircleDomains.Probability.PathOccupation

namespace OAI

/-! A constant density on an open region pays the length of a rectifiable
passage that lies in that region apart from its last endpoint. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem indicator_occupation_of_interior_passage
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O) (a : ℝ≥0∞) :
    (∫⁻y, O.indicator (fun _ => a) y ∂pathOccupation γ) = a * eVariationOn γ.val univ := by
  rw [lintegral_pathOccupation γ (measurable_const.indicator hO)]
  have hae : ∀ᵐ t ∂pathLengthMeasure γ, O.indicator (fun _ => a) (γ.val t) = a := by
    have hn := (measure_eq_zero_iff_ae_notMem).mp
      (measure_singleton (μ := pathLengthMeasure γ) (⊤ : PathTime))
    filter_upwards [hn] with t ht
    have hne : t ≠ ⊤ := by simpa only [mem_singleton_iff] using ht
    exact Set.indicator_of_mem (hinside t (lt_top_iff_ne_top.mpr hne)) (fun _ => a)
  rw [lintegral_congr_ae hae, lintegral_const, pathLengthMeasure_univ]

theorem indicator_occupation_pays_endpoint_distance
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : δ ≤ edist (γ.val ⊥) (γ.val ⊤)) :
    1 ≤ ∫⁻y, O.indicator (fun _ => δ⁻¹) y ∂pathOccupation γ := by
  rw [indicator_occupation_of_interior_passage γ O hO hinside]
  calc
    1 = δ⁻¹ * δ := (ENNReal.inv_mul_cancel hδ hδfin).symm
    _ ≤ δ⁻¹ * eVariationOn γ.val univ :=
      mul_le_mul' le_rfl (hsep.trans (eVariationOn.edist_le γ.val (mem_univ _) (mem_univ _)))

end CircleDomainRigidity

end

end OAI
