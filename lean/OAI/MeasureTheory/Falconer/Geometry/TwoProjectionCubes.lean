import OAI.MeasureTheory.Falconer.Geometry.ProjectionCube

namespace OAI

/-! # Compatible unit-cube normalization of two successive projections -/
namespace Falconer
open Set MeasureTheory
variable {d m k : ℕ}

theorem two_projections_into_unitCubes (E : Set (Space d)) (hE : IsCompact E)
    (P : Space d →L[ℝ] Space m) (Q : Space m →L[ℝ] Space k) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ‖a • P‖ ≤ 1 ∧ ‖b • Q‖ ≤ 1 ∧
      (∀ x ∈ E, (a • P) x ∈ (centeredUnitCube m).carrier) ∧
      (∀ x ∈ E, ((b • Q).comp (a • P)) x ∈ (centeredUnitCube k).carrier) := by
  obtain ⟨a,ha,hP,hroot⟩ := compact_projection_into_unitCube E hE P
  obtain ⟨b,hb,hQ,hroot'⟩ := compact_projection_into_unitCube ((a • P) '' E)
    (hE.image (a • P).continuous) Q
  exact ⟨a,b,ha,hb,hP,hQ,hroot,fun x hx => hroot' _ ⟨x,hx,rfl⟩⟩

theorem scaled_composite {a b : ℝ} (P : Space d →L[ℝ] Space m)
    (Q : Space m →L[ℝ] Space k) :
    (b • Q).comp (a • P) = (a*b) • (Q.comp P) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,smul_apply,map_smul,smul_smul]

end Falconer

end OAI
