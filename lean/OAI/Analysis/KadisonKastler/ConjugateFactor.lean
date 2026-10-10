import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Factor transport and composition for a conjugated neighbor -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inner automorphism restricted to the original algebra. -/
def unitaryConjugateHom (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    Algebra N →⋆ₐ[ℂ] Algebra (unitaryConjugateAlgebra w N) :=
  ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).toStarAlgHom.comp
    N.toStarSubalgebra.subtype).codRestrict
      (unitaryConjugateAlgebra w N).toStarSubalgebra (fun x => ⟨x.val, x.property, rfl⟩)

@[simp]
theorem unitaryConjugateHom_apply (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) (x : Algebra N) :
    (unitaryConjugateHom w N x : H →L[ℂ] H) = unitaryConj w x := rfl

theorem unitaryConjugateHom_bijective (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) : Function.Bijective (unitaryConjugateHom w N) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w).injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Exact star-algebra equivalence with the conjugated concrete algebra. -/
def unitaryConjugateEquiv (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    Algebra N ≃⋆ₐ[ℂ] Algebra (unitaryConjugateAlgebra w N) :=
  StarAlgEquiv.ofBijective (unitaryConjugateHom w N) (unitaryConjugateHom_bijective w N)

@[simp]
theorem unitaryConjugateEquiv_apply (w : unitary (H →L[ℂ] H))
    (N : VonNeumannAlgebra H) (x : Algebra N) :
    (unitaryConjugateEquiv w N x : H →L[ℂ] H) = unitaryConj w x := rfl

/-- The finite diffuse factor predicate is preserved by unitary conjugation. -/
theorem unitaryConjugateAlgebra_isII1 (w : unitary (H →L[ℂ] H))
    {N : VonNeumannAlgebra H} (hN : Generator.IsII1Factor N.toStarSubalgebra) :
    Generator.IsII1Factor (unitaryConjugateAlgebra w N).toStarSubalgebra :=
  Generator.isII1Factor_of_starAlgEquiv (unitaryConjugateEquiv w N) hN
    (Generator.Tracial.traceHilbertVonNeumann_wotClosed (unitaryConjugateAlgebra w N))

/-- Return from the moved neighbor to the original one by composing unitaries. -/
theorem conjugates_of_conjugated_neighbor {M N : VonNeumannAlgebra H}
    (w v : unitary (H →L[ℂ] H))
    (hv : Conjugates v M (unitaryConjugateAlgebra (star w) N)) :
    Conjugates (w * v) M N := by
  have hw : Conjugates w (unitaryConjugateAlgebra (star w) N) N := by
    simpa only [star_star] using (conjugates_unitaryConjugateAlgebra (star w) N).symm
  exact hv.trans hw

/-- The final displacement includes the initial movement of the neighbor. -/
theorem conjugated_neighbor_displacement_le (w v : unitary (H →L[ℂ] H)) :
    ‖((w * v : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ ≤
      ‖(w : H →L[ℂ] H) - 1‖ + ‖(v : H →L[ℂ] H) - 1‖ :=
  norm_unitary_mul_sub_one_le w v

end

end KadisonKastler

end OAI
