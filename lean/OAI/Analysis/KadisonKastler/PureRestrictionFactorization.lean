import OAI.Analysis.KadisonKastler.PureCommutingCompression

namespace OAI

/-! # Product values from a pure restriction

An ambient state whose restriction to one algebra is pure factors
against every element commuting with that algebra.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem pure_restriction_commuting_factorization
    (ι : A →⋆ₐ[ℂ] B) (φ : B →L[ℂ] ℂ) (hφ : IsState φ)
    (hpure : IsPureState (restrictState ι φ))
    (b : B) (hb : ∀ a : A, Commute b (ι a)) (a : A) :
    φ (ι a*b)=φ (ι a)*φ b := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let P := positiveOfSquares φ hφ.2
  let π := P.gnsStarAlgHom.comp ι
  let ξ := gnsVector P
  have hξ : ‖ξ‖=1 := gnsVector_norm_eq_one P ((isState_iff φ).mp hφ).1
  have hstate : NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ=restrictState ι φ := by
    ext c
    exact gnsVector_coefficient P (ι c)
  have hp : IsPureState (NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ) := by
    rwa [hstate]
  have hc (c : A) : Commute (P.gnsStarAlgHom b) (π c) :=
    (hb c).map P.gnsStarAlgHom
  have h := pureVector_commuting_factorization π ξ hξ hp (P.gnsStarAlgHom b) hc a
  calc
    φ (ι a*b) = inner ℂ ξ (P.gnsStarAlgHom (ι a*b) ξ) :=
      (gnsVector_coefficient P (ι a*b)).symm
    _ = inner ℂ ξ (π a (P.gnsStarAlgHom b ξ)) := by
      rw [map_mul]
      rfl
    _ = inner ℂ ξ (π a ξ)*inner ℂ ξ (P.gnsStarAlgHom b ξ) := h
    _ = φ (ι a)*φ b := by
      change inner ℂ ξ (P.gnsStarAlgHom (ι a) ξ)*
        inner ℂ ξ (P.gnsStarAlgHom b ξ)=_
      rw [gnsVector_coefficient,gnsVector_coefficient]
      rfl

end

end KadisonKastler

end OAI
