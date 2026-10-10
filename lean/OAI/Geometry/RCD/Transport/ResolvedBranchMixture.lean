import OAI.Geometry.RCD.Transport.ResolvedSubplanOptimality

namespace OAI

/-! # The half mixture as an actual resolved paired subplan -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

def diagonalFirst (z : C(Time,X)×C(Time,X)) : C(Time,X)×C(Time,X) := (z.1,z.1)

def halfResolvedPair (σ : Measure (C(Time,X)×C(Time,X))) :
    Measure (C(Time,X)×C(Time,X)) := (2:ℝ≥0∞)⁻¹ • (σ.map diagonalFirst + σ)

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem measurable_diagonalFirst : Measurable (diagonalFirst (X:=X)) :=
  measurable_fst.prodMk measurable_fst

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem resolvePathBranch_diagonal (q : Time) (γ : C(Time,X)) :
    resolvePathBranch q (γ,γ)=γ := by
  ext t
  exact (resolvePathBranch_choice q (γ,γ) t).elim id id

omit [MetricSpace X] [BorelSpace X] [SeparableSpace X] in
theorem half_smul_self (μ : Measure X) : (2:ℝ≥0∞)⁻¹ • (μ+μ)=μ := by
  rw [←two_smul ℝ≥0∞ μ,smul_smul]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_smul]

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem diagonalFirst_fst (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map diagonalFirst).map Prod.fst=σ.map Prod.fst := by
  rw [Measure.map_map measurable_fst measurable_diagonalFirst]
  rfl

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem diagonalFirst_snd (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map diagonalFirst).map Prod.snd=σ.map Prod.fst := by
  rw [Measure.map_map measurable_snd measurable_diagonalFirst]
  rfl

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem halfResolvedPair_fst (σ : Measure (C(Time,X)×C(Time,X))) :
    (halfResolvedPair σ).map Prod.fst=σ.map Prod.fst := by
  rw [halfResolvedPair,Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_add _ _ measurable_fst,diagonalFirst_fst]
  exact half_smul_self _

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem halfResolvedPair_snd (σ : Measure (C(Time,X)×C(Time,X))) :
    (halfResolvedPair σ).map Prod.snd=(2:ℝ≥0∞)⁻¹ • (σ.map Prod.fst+σ.map Prod.snd) := by
  rw [halfResolvedPair,Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_add _ _ measurable_snd,diagonalFirst_snd]

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem halfResolvedPair_mass (σ : Measure (C(Time,X)×C(Time,X))) :
    halfResolvedPair σ univ=σ univ := by
  have h := congrArg (fun μ : Measure C(Time,X) => μ univ) (halfResolvedPair_fst σ)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ] using h

instance halfResolvedPair_finite (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] :
    IsFiniteMeasure (halfResolvedPair σ) :=
  ⟨by rw [halfResolvedPair_mass]; exact measure_lt_top _ _⟩

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem halfResolvedPair_dominated (σ : Measure (C(Time,X)×C(Time,X)))
    (π : Measure C(Time,X)) (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) :
    (halfResolvedPair σ).map Prod.fst ≤ π ∧ (halfResolvedPair σ).map Prod.snd ≤ π := by
  constructor
  · simpa only [halfResolvedPair_fst] using hl
  · rw [halfResolvedPair_snd]
    exact (smul_le_smul_left ((2:ℝ≥0∞)⁻¹) (add_le_add hl hr)).trans_eq (half_smul_self π)

theorem diagonalFirst_resolved (σ : Measure (C(Time,X)×C(Time,X))) (q : Time) :
    (σ.map diagonalFirst).map (resolvePathBranch q)=σ.map Prod.fst := by
  rw [Measure.map_map (measurable_resolvePathBranch q) measurable_diagonalFirst]
  congr 1
  funext z
  exact resolvePathBranch_diagonal q z.1

theorem halfResolvedPair_resolved (σ : Measure (C(Time,X)×C(Time,X))) (q : Time) :
    (halfResolvedPair σ).map (resolvePathBranch q)=
      (2:ℝ≥0∞)⁻¹ • (σ.map Prod.fst+σ.map (resolvePathBranch q)) := by
  rw [halfResolvedPair,Measure.map_smul _ (measurable_resolvePathBranch q).aemeasurable,
    Measure.map_add _ _ (measurable_resolvePathBranch q),diagonalFirst_resolved]

theorem normalized_halfResolvedPair (σ : Measure (C(Time,X)×C(Time,X))) (q : Time) :
    (((halfResolvedPair σ) univ)⁻¹ • halfResolvedPair σ).map (resolvePathBranch q)=
      (2:ℝ≥0∞)⁻¹ • (((σ univ)⁻¹ • σ).map Prod.fst+
        ((σ univ)⁻¹ • σ).map (resolvePathBranch q)) := by
  rw [halfResolvedPair_mass,Measure.map_smul _ (measurable_resolvePathBranch q).aemeasurable,
    halfResolvedPair_resolved,Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ (measurable_resolvePathBranch q).aemeasurable,
    smul_comm,smul_add]

end RegularPointCoordinates

end

end OAI
