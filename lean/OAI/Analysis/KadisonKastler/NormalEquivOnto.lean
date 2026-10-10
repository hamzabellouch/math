import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # A normal representation equivalence with a specified concrete range -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
  (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
  (hfaith : Function.Injective φ) (hφ : BoundedWeakNormal M φ)
  (hmem : ∀ a, φ a ∈ N) (hrange : generatedVonNeumannAlgebra φ.range = N)

def normalEquivOnto : Algebra M ≃⋆ₐ[ℂ] Algebra N := by
  let f : Algebra M →⋆ₐ[ℂ] Algebra N := φ.codRestrict N.toStarSubalgebra hmem
  apply StarAlgEquiv.ofBijective f
  constructor
  · intro a b h
    exact hfaith (congrArg Subtype.val h)
  · intro b
    have hb : b.val ∈ generatedVonNeumannAlgebra φ.range := by
      rw [hrange]
      exact b.property
    obtain ⟨a, ha⟩ := boundedWeakNormal_surjective_generated M φ hfaith hφ b.val hb
    exact ⟨a, Subtype.ext ha⟩

theorem normalEquivOnto_val (a : Algebra M) :
    (normalEquivOnto M N φ hfaith hφ hmem hrange a).val = φ a := rfl

theorem normalEquivOnto_boundedWeakNormal :
    BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp
      (normalEquivOnto M N φ hfaith hφ hmem hrange).toStarAlgHom) := by
  intro ι l a b C hn hw x y
  exact hφ a b C hn hw x y

include φ hfaith hφ hmem hrange in
theorem exists_normalEquivOnto :
    ∃ e : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp e.toStarAlgHom) :=
  ⟨normalEquivOnto M N φ hfaith hφ hmem hrange,
    normalEquivOnto_boundedWeakNormal M N φ hfaith hφ hmem hrange⟩

end

end KadisonKastler

end OAI
