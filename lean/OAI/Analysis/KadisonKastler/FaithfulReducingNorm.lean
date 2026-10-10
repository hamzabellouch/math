import OAI.Analysis.KadisonKastler.ReducingCommutantCorner

namespace OAI

/-! # Norms in nonzero reducing representations of a simple algebra -/

namespace KadisonKastler

noncomputable section

universe u

variable {B H : Type u} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
  (hE : ∀ b, E.starProjection * π b = π b * E.starProjection)

def reducingRepresentation : B →⋆ₐ[ℂ] (E →L[ℂ] E) :=
  (reducingRestriction E π.range (by
    rintro ⟨T, b, rfl⟩
    exact invariant_of_commutes_starProjection E (π b) (hE b))).comp
      (π.codRestrict π.range (fun b => ⟨b, rfl⟩))

theorem reducingRepresentation_apply (b : B) :
    reducingRepresentation E π hE b = cornerCompression E (π b) := rfl

include hE in
theorem norm_reducingRepresentation [Nontrivial E] [Nontrivial H]
    (hB : ∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
      (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ) (b : B) :
    ‖cornerCompression E (π b)‖ = ‖π b‖ := by
  change ‖reducingRepresentation E π hE b‖ = ‖π b‖
  have hρ : Function.Injective (reducingRepresentation E π hE) :=
    hB (E →L[ℂ] E) (reducingRepresentation E π hE)
  have hπ : Function.Injective π := hB (H →L[ℂ] H) π
  exact (NonUnitalStarAlgHom.norm_map (reducingRepresentation E π hE).toNonUnitalStarAlgHom
    hρ b).trans (NonUnitalStarAlgHom.norm_map π.toNonUnitalStarAlgHom hπ b).symm

end

end KadisonKastler

end OAI
