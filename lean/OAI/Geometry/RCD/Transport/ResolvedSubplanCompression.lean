import OAI.Geometry.RCD.Transport.ResolvedSubplanOptimality

namespace OAI

/-! # Density and support bounds for normalized resolved subplans -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_resolved_compression (μ : Measure X) (π : Measure C(Time,X))
    (σ : Measure (C(Time,X)×C(Time,X)))
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    {C : ℝ≥0∞} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (q t : Time) :
    (((σ univ)⁻¹ • σ).map (resolvePathBranch q)).map (fun γ => γ t) ≤
      (2*((σ univ)⁻¹*C)) • μ := by
  let c := (σ univ)⁻¹
  have hside (f : C(Time,X)×C(Time,X) → C(Time,X)) (hf : Measurable f)
      (hdom : σ.map f ≤ π) :
      ((c • σ).map f).map (fun γ => γ t) ≤ (c*C) • μ := by
    rw [Measure.map_map (measurable_path_eval t) hf,
      Measure.map_smul _ ((measurable_path_eval t).comp hf).aemeasurable]
    have hmap : σ.map ((fun γ => γ t) ∘ f) ≤ π.map (fun γ => γ t) := by
      rw [←Measure.map_map (measurable_path_eval t) hf]
      exact Measure.map_mono hdom (measurable_path_eval t)
    exact (smul_le_smul_left c hmap).trans (by simpa only [smul_smul] using smul_le_smul_left c (hc t))
  have hsum := add_le_add (hside Prod.fst measurable_fst hl) (hside Prod.snd measurable_snd hr)
  have h := (resolved_branch_compression q (c • σ) t).trans hsum
  simpa only [←add_smul,←two_mul] using h

theorem normalized_resolved_endpoint_support (π : Measure C(Time,X))
    (σ : Measure (C(Time,X)×C(Time,X))) (hr : σ.map Prod.snd ≤ π)
    (q t : Time) (ht : t=0 ∨ t=1) {p : X} {R : ℝ}
    (hs : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ R) :
    ∀ᵐ x ∂(((σ univ)⁻¹ • σ).map (resolvePathBranch q)).map (fun γ => γ t), dist x p ≤ R := by
  rw [resolved_branch_endpoint_time q _ t ht,
    Measure.map_map (measurable_path_eval t) measurable_snd]
  have hm : Measurable (fun z : C(Time,X)×C(Time,X) => z.2 t) :=
    (measurable_path_eval t).comp measurable_snd
  change ∀ᵐ x ∂((σ univ)⁻¹ • σ).map (fun z => z.2 t), dist x p ≤ R
  rw [Measure.map_smul _ hm.aemeasurable]
  have hdom : σ.map (fun z => z.2 t) ≤ π.map (fun γ => γ t) := by
    simpa only [Measure.map_map (measurable_path_eval t) measurable_snd,Function.comp_def] using
      Measure.map_mono hr (measurable_path_eval t)
  exact (hs.filter_mono hdom.absolutelyContinuous.ae_le).filter_mono
    Measure.smul_absolutelyContinuous.ae_le

end RegularPointCoordinates

end

end OAI
