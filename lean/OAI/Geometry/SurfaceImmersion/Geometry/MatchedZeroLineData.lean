import OAI.Geometry.SurfaceImmersion.Atlas.ZeroSliceLineChart

namespace OAI

/-! Retain the coordinate formulas for the real chart on a matched zero set. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

theorem matched_zero_subset_line_chart_data (e : OpenPartialHomeomorph X (E × ℝ))
    (S : Set X) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = 0) :
    ∃ c : OpenPartialHomeomorph S ℝ,
      (⟨p,hpS⟩ : S) ∈ c.source ∧
      c.source = ((↑) ⁻¹' e.source) ∧
      c.target = {t | (0,t) ∈ e.target} ∧
      (∀ x ∈ c.source, c x = (e x.val).2) ∧
      (∀ t ∈ c.target, (c.symm t).val = e.symm (0,t)) := by
  obtain ⟨a,ha,has,hat,haf,hag⟩ :=
    matched_subset_chart e S {z | z.1 = 0} p hp hpS hmatch
  let h := (zeroSliceLineHomeomorph (E := E)).toOpenPartialHomeomorph
  let c := a.trans h
  have hcs : c.source = a.source := by
    ext x
    simp [c,h]
  have hct : c.target = {t | (0,t) ∈ e.target} := by
    ext t
    simp [c,h,hat,zeroSliceLineHomeomorph]
  refine ⟨c,?_,hcs.trans has,hct,?_,?_⟩
  · rw [hcs]
    exact ha
  · intro x hx
    change (a x).val.2 = (e x.val).2
    rw [haf x (hcs ▸ hx)]
  · intro t ht
    change (a.symm ⟨(0,t),rfl⟩).val = e.symm (0,t)
    apply hag
    rw [hat]
    change (0,t) ∈ e.target
    rw [hct] at ht
    exact ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
