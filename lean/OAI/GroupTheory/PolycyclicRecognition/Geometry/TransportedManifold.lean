import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace OAI

/-! # Pulling a smooth atlas back through a homeomorphism -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace E M]

/-- A pullback atlas whose preferred charts have explicit formulas. -/
@[instance_reducible]
def pullbackChartedSpace (e : X ≃ₜ M) : ChartedSpace E X where
  atlas := {c | ∃ y : M, c = e.transOpenPartialHomeomorph (chartAt E y)}
  chartAt x := e.transOpenPartialHomeomorph (chartAt E (e x))
  mem_chart_source x := mem_chart_source E (e x)
  chart_mem_atlas x := ⟨e x,rfl⟩

variable (e : X ≃ₜ M)

theorem pullback_isManifold [IsManifold (𝓘(ℝ,E)) ∞ M] :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    IsManifold (𝓘(ℝ,E)) ∞ X := by
  let cs : ChartedSpace E X := pullbackChartedSpace (E := E) e
  refine { compatible := ?_ }

  rintro c c' ⟨y,rfl⟩ ⟨z,rfl⟩
  have he : (e.transOpenPartialHomeomorph (chartAt E y)).symm.trans
      (e.transOpenPartialHomeomorph (chartAt E z)) =
      (chartAt E y).symm.trans (chartAt E z) := by
    apply OpenPartialHomeomorph.ext
    · intro v
      change (chartAt E z) (e (e.symm ((chartAt E y).symm v))) =
        (chartAt E z) ((chartAt E y).symm v)
      rw [e.apply_symm_apply]
    · intro v
      change (chartAt E y) (e (e.symm ((chartAt E z).symm v))) =
        (chartAt E y) ((chartAt E z).symm v)
      rw [e.apply_symm_apply]
    · ext v
      simp [Homeomorph.transOpenPartialHomeomorph, Function.comp_def]
  rw [he]
  exact StructureGroupoid.compatible (contDiffGroupoid ∞ (𝓘(ℝ,E))) (chart_mem_atlas E y) (chart_mem_atlas E z)
theorem contMDiff_pullback :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e := by
  let cs : ChartedSpace E X := pullbackChartedSpace (E := E) e
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt,?_⟩
  have hi := (contMDiff_id : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (id : M → M)) (e x)
  rw [contMDiffAt_iff] at hi
  have hr : Set.range (𝓘(ℝ,E)) = Set.univ := by ext v; simp
  rw [hr]
  change ContDiffWithinAt ℝ ∞
    (fun v => (chartAt E (e x)) (e (e.symm ((chartAt E (e x)).symm v))))
    Set.univ ((chartAt E (e x)) (e x))
  simpa only [mfld_simps, Function.comp_def, Homeomorph.apply_symm_apply] using hi.2

theorem contMDiff_pullback_symm :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e.symm := by
  let cs : ChartedSpace E X := pullbackChartedSpace (E := E) e
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.symm.continuous.continuousAt,?_⟩
  have hi := (contMDiff_id : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (id : M → M)) x
  rw [contMDiffAt_iff] at hi
  have hr : Set.range (𝓘(ℝ,E)) = Set.univ := by ext v; simp
  rw [hr]
  change ContDiffWithinAt ℝ ∞
    (fun v => (chartAt E (e (e.symm x))) (e (e.symm ((chartAt E x).symm v))))
    Set.univ ((chartAt E x) x)
  simpa only [mfld_simps, Function.comp_def, Homeomorph.apply_symm_apply] using hi.2

end PolycyclicRecognition

end

end OAI
