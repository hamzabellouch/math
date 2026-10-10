import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.CuntzBasic

namespace OAI

section

namespace UnitalTomsWinter
variable {A B : Type*} [CStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem CuntzSubequiv.reflect_corner (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (hcorner : ∀ x : B, φ 1 * x * φ 1 = x → ∃ y : A, φ y = x)
    {a b : A} (hcomp : CuntzSubequiv (φ a) (φ b)) : CuntzSubequiv a b := by
  have hq : IsStarProjection (φ 1) := by
    constructor
    · change φ 1 * φ 1 = φ 1
      rw [← map_mul, one_mul]
    · change star (φ 1) = φ 1
      rw [← map_star, star_one]
  have hleft (c : A) : φ 1 * φ c = φ c := by rw [← map_mul, one_mul]
  have hright (c : A) : φ c * φ 1 = φ c := by rw [← map_mul, mul_one]
  apply cuntzSubequiv_iff_norm.mpr
  intro ε hε
  obtain ⟨x, hxl, hxr, hx⟩ := hcomp.exists_corner_witness hq hq
    (hleft b) (hright b) (hleft a) (hright a) hε
  obtain ⟨y, hy⟩ := hcorner x (by rw [hxl, hxr])
  refine ⟨y, ?_⟩
  have heq : star x * φ b * x - φ a = φ (star y * b * y - a) := by
    rw [← hy, map_sub, map_mul, map_mul, map_star]
  rw [heq, NonUnitalStarAlgHom.norm_map φ hφ] at hx
  exact hx
end UnitalTomsWinter
end

end OAI
