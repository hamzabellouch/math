import OAI.Geometry.RCD.Transport.ResolvedBranchMixture

namespace OAI

/-! # Equal and singular marginals of normalized paired branch laws -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] in
theorem normalized_pair_left_eval (σ : Measure (C(Time,X)×C(Time,X))) (t : Time) :
    (((σ univ)⁻¹ • σ).map Prod.fst).map (fun γ => γ t)=
      (σ univ)⁻¹ • σ.map (fun z => z.1 t) := by
  rw [Measure.map_map (measurable_path_eval t) measurable_fst]
  exact Measure.map_smul _ ((measurable_path_eval t).comp measurable_fst).aemeasurable

theorem normalized_pair_right_eval (σ : Measure (C(Time,X)×C(Time,X))) (q t : Time) :
    (((σ univ)⁻¹ • σ).map (resolvePathBranch q)).map (fun γ => γ t)=
      (σ univ)⁻¹ • σ.map (fun z => resolvePathBranch q z t) := by
  rw [Measure.map_map (measurable_path_eval t) (measurable_resolvePathBranch q)]
  exact Measure.map_smul _ ((measurable_path_eval t).comp (measurable_resolvePathBranch q)).aemeasurable

theorem normalized_pair_eval_eq (σ : Measure (C(Time,X)×C(Time,X))) (q t : Time)
    (he : σ.map (fun z => z.1 t)=σ.map (fun z => resolvePathBranch q z t)) :
    (((σ univ)⁻¹ • σ).map Prod.fst).map (fun γ => γ t)=
      (((σ univ)⁻¹ • σ).map (resolvePathBranch q)).map (fun γ => γ t) := by
  rw [normalized_pair_left_eval,normalized_pair_right_eval,he]

theorem normalized_pair_eval_singular (σ : Measure (C(Time,X)×C(Time,X))) (q t : Time)
    (hs : σ.map (fun z => z.1 t) ⟂ₘ σ.map (fun z => resolvePathBranch q z t)) :
    (((σ univ)⁻¹ • σ).map Prod.fst).map (fun γ => γ t) ⟂ₘ
      (((σ univ)⁻¹ • σ).map (resolvePathBranch q)).map (fun γ => γ t) := by
  rw [normalized_pair_left_eval,normalized_pair_right_eval]
  exact ((hs.smul _).symm.smul _).symm

omit [SeparableSpace X] in
theorem half_mixture_map_eval (τ₀ τ₁ : Measure C(Time,X)) (t : Time) :
    ((2:ℝ≥0∞)⁻¹ • (τ₀+τ₁)).map (fun γ => γ t)=
      (2:ℝ≥0∞)⁻¹ • (τ₀.map (fun γ => γ t)+τ₁.map (fun γ => γ t)) := by
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable,
    Measure.map_add _ _ (measurable_path_eval t)]

omit [SeparableSpace X] in
theorem half_mixture_eval_eq (τ₀ τ₁ : Measure C(Time,X)) (t : Time)
    (he : τ₀.map (fun γ => γ t)=τ₁.map (fun γ => γ t)) :
    ((2:ℝ≥0∞)⁻¹ • (τ₀+τ₁)).map (fun γ => γ t)=τ₀.map (fun γ => γ t) := by
  rw [half_mixture_map_eval,←he,half_smul_self]

end RegularPointCoordinates

end

end OAI
