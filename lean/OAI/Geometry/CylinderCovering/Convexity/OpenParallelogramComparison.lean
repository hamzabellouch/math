import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogram
import OAI.Geometry.CylinderCovering.Convexity.OpenBaseComparison

namespace OAI

noncomputable section
open Set

namespace RuledApproximation

theorem openParallelogram_of_strict_half {n : ℕ} (C : Fin n → Cylinder)
    (S : Set Space) {m : ℝ} (hC : ∀ i, (C i).parallelogram)
    (hcover : S ⊆ familySet C) (hm : 0 < m)
    (hshadow : ∀ i, m ≤ (C i).shadowArea S) (hcost : familyArea C < m / 2) :
    ∃ D : Fin n → Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openParallelogram ∧ (D i).openBounded) ∧
      S ⊆ familySet D ∧ familyArea D < m / 2 ∧ familyRelativeArea D S < 1 / 2 := by
  obtain ⟨D,haxis,hshape,hCD,harea⟩ :=
    finite_enlarge_openParallelogram C hC (sub_pos.mpr hcost)
  have hDcost : familyArea D < m / 2 := by linarith
  refine ⟨D,haxis,hshape,hcover.trans hCD,hDcost,?_⟩
  apply familyRelativeArea_lt_half D S hm _ hDcost
  intro i
  rw [Cylinder.shadowArea_eq_of_axis_eq (haxis i) S]
  exact hshadow i

end RuledApproximation

end

end OAI
