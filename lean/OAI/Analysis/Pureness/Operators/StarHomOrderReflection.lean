import OAI.Analysis.Pureness.Divisibility.CornerRanks
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem nonUnitalStarAlgHom_nonneg_iff (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) (a : A) :
    0 ≤ φ a ↔ 0 ≤ a := by
  constructor
  · intro ha
    let s : NonUnitalStarSubalgebra ℂ B := NonUnitalStarAlgHom.range φ
    have hs : IsClosed (s : Set B) := (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
    let : IsClosed (s : Set B) := hs
    have hm : CFC.sqrt (φ a) ∈ s := by
      rw [CFC.sqrt_eq_nnrpow, CFC.nnrpow_eq_cfcₙ_real _ _ ha]
      exact cfcₙ_mem (𝕜' := ℂ) _ (NonUnitalStarAlgHom.mem_range_self φ a)
    obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range φ).mp hm
    have he : star x * x = a := hφ (by
      rw [map_mul, map_star, hx, (CFC.sqrt_nonneg (φ a)).star_eq, CFC.sqrt_mul_sqrt_self (φ a) ha])
    rw [← he]
    exact star_mul_self_nonneg _
  · intro ha
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he, map_mul, map_star]
    exact star_mul_self_nonneg _
end CuntzPureness

end OAI
