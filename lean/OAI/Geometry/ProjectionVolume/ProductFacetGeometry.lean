import OAI.Geometry.ProjectionVolume.ProductProjection

namespace OAI

open Set

namespace Paper092

theorem productFacet_inl_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inl a) = splitBlocks ⁻¹' (simplexFacet 10 a ×ˢ standardSimplex 10) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (firstBlock x) a = 0) ↔
      ((firstBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (firstBlock x) a = 0) ∧
        secondBlock x ∈ standardSimplex 10)
  exact ⟨fun ⟨⟨hx, hy⟩, ha⟩ => ⟨⟨hx, ha⟩, hy⟩,
    fun ⟨⟨hx, ha⟩, hy⟩ => ⟨⟨hx, hy⟩, ha⟩⟩

theorem productFacet_inr_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inr a) = splitBlocks ⁻¹' (standardSimplex 10 ×ˢ simplexFacet 10 a) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (secondBlock x) a = 0) ↔
      (firstBlock x ∈ standardSimplex 10 ∧
        (secondBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (secondBlock x) a = 0))
  exact and_assoc

end Paper092

end OAI
