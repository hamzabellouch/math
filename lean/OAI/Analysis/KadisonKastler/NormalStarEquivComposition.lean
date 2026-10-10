import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # Composition of the specified normal representation changes -/

namespace KadisonKastler

open Filter

noncomputable section

universe u

variable {H K L : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {P : VonNeumannAlgebra L}

theorem boundedWeakNormal_starEquiv_trans
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (f : Algebra N ≃⋆ₐ[ℂ] Algebra P)
    (he : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp e.toStarAlgHom))
    (hf : BoundedWeakNormal N (P.toStarSubalgebra.subtype.comp f.toStarAlgHom)) :
    BoundedWeakNormal M (P.toStarSubalgebra.subtype.comp (e.trans f).toStarAlgHom) := by
  intro ι l a b C hn hw
  apply hf (fun i => e (a i)) (e b) C
  · filter_upwards [hn] with i hi
    exact (NonUnitalStarAlgHom.norm_apply_le e (a i)).trans hi
  · exact he a b C hn hw

end

end KadisonKastler

end OAI
