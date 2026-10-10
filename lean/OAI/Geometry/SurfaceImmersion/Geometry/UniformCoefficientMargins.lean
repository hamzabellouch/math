import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! A common quantitative trial radius for varying grid coefficient forms. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseMean
open SmallModes (Base)

theorem uniform_coefficient_margins {a C H : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
      ∀ (Q : Tensor →L[ℝ] ℝ), ‖Q‖ ≤ C →
      ∀ reference : Base → Tensor, Continuous reference →
      (∀ x, Q (reference x) ≤ H) → ∀ K : Set Base,
      (∀ x ∈ K, a ≤ Q (reference x)) →
      ∃ W : Set Base, IsOpen W ∧ K ⊆ W ∧
        ∀ x ∈ W, ρ+‖Q‖*r ≤ Q (reference x) ∧
          Q (reference x) ≤ R-‖Q‖*r := by
  let r : ℝ := (a/8)/(C+1)
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hCr : (C+1)*r = a/8 := by
    dsimp [r]
    field_simp
  refine ⟨r,a/8,H+a/8+1,hr,by linarith,by linarith,?_⟩
  intro Q hQ reference href hu K hl
  let W : Set Base := {x | a/2 < Q (reference x)}
  have hW : IsOpen W := isOpen_lt continuous_const (Q.continuous.comp href)
  have hKW : K ⊆ W := fun x hx => lt_of_lt_of_le (by linarith) (hl x hx)
  have hnr : ‖Q‖*r ≤ a/8 :=
    (mul_le_mul_of_nonneg_right hQ hr.le).trans (by nlinarith)
  refine ⟨W,hW,hKW,?_⟩
  intro x hx
  have hlx : a/2 < Q (reference x) := hx
  have hux := hu x
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
