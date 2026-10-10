import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import OAI.Geometry.RCD.Sobolev.OrthonormalImageSpan

namespace OAI

/-! # A unit outward support vector at a boundary point of a convex image -/

open Set
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem convex_unit_support {n : ℕ} (S : Set (Euclidean n)) (hS : Convex ℝ S)
    (hSi : (interior S).Nonempty) {p : Euclidean n} (hp : p∉interior S) :
    ∃ a : Euclidean n, ‖a‖=1 ∧ ∀ z∈S, ⟪z-p,a⟫_ℝ≤0 := by
  obtain ⟨f,hf,hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point hS hp hSi
  let a₀ := (InnerProductSpace.toDual ℝ (Euclidean n)).symm f
  have ha₀ : a₀≠0 := by
    intro hz
    apply hf
    calc
      f = InnerProductSpace.toDual ℝ (Euclidean n) a₀ :=
        ((InnerProductSpace.toDual ℝ (Euclidean n)).apply_symm_apply f).symm
      _ = 0 := by rw [hz]; exact map_zero _
  have hn : 0<‖a₀‖ := norm_pos_iff.mpr ha₀
  refine ⟨‖a₀‖⁻¹ • a₀,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · intro z hz
    have he : ⟪z-p,a₀⟫_ℝ=f z-f p := by
      rw [real_inner_comm,inner_sub_right]
      exact congrArg₂ (·-·) (InnerProductSpace.toDual_symm_apply)
        (InnerProductSpace.toDual_symm_apply)
    rw [inner_smul_right,he]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hn).le (sub_nonpos.mpr (hbound z hz))

end RegularPointCoordinates

end

end OAI
