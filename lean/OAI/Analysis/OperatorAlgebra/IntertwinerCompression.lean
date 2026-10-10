import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression

namespace OAI

/-! A compressed commuting action still commutes with the intertwined action. -/
noncomputable section
namespace WeakPureInfiniteness

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma intertwiner_adjoint (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V) (a : A) :
    (ρ a).comp V.adjoint = V.adjoint.comp (π a) := by
  have h := congrArg ContinuousLinearMap.adjoint (hV (star a))
  simpa only [ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star] using h

lemma intertwiner_compression_commutes (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (T : H →L[ℂ] H) (hT : ∀ a, Commute (π a) T) (a : A) :
    Commute (ρ a) (V.adjoint.comp (T.comp V)) := by
  apply (commute_iff_eq _ _).mpr
  apply ContinuousLinearMap.ext
  intro x
  have hadj := congrArg (fun W : H →L[ℂ] K => W (T (V x)))
    (intertwiner_adjoint ρ π V hV a)
  have hvec := congrArg (fun W : K →L[ℂ] H => W x) (hV a)
  have hcomm := congrArg (fun W : H →L[ℂ] H => W (V x)) (hT a).eq
  change ρ a (V.adjoint (T (V x))) = V.adjoint (T (V (ρ a x)))
  exact hadj.trans (congrArg V.adjoint (hcomm.trans (congrArg T hvec.symm)))

end WeakPureInfiniteness

end

end OAI
