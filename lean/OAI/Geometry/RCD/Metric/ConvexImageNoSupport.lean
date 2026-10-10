import OAI.Geometry.RCD.Metric.ConvexUnitSupport

namespace OAI

/-! # A convex image with no supporting direction has interior -/

open Set
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem convex_image_interior_of_no_support {Y : Type*} {n : ℕ}
    (F : Y → Euclidean n) (S : Set Y) (hconv : Convex ℝ (F '' S))
    {q : Y} (hq : q∈S)
    (hno : ∀ a : Euclidean n, ‖a‖=1 → (∀ y∈S, ⟪F y-F q,a⟫_ℝ≤0) → False) :
    (interior (F '' S)).Nonempty := by
  apply hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
  apply affineSpan_eq_top_of_linear_constants (F '' S) ⟨F q,q,hq,rfl⟩
  intro a c hconstant
  by_contra ha
  have hn : 0<‖a‖ := norm_pos_iff.mpr ha
  apply hno (‖a‖⁻¹ • a)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · intro y hy
    rw [inner_smul_right,inner_sub_left,hconstant (F y) ⟨y,hy,rfl⟩,
      hconstant (F q) ⟨q,hq,rfl⟩,sub_self,mul_zero]

end RegularPointCoordinates

end

end OAI
