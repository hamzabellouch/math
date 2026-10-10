import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

lemma conjugate_inverse (T : K →L[ℂ] K) :
    U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T)=T := by
  ext v
  simp

lemma conjugate_commutator (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T)=
      T*U.conjStarAlgEquiv a-U.conjStarAlgEquiv a*T := by
  rw [map_sub,map_mul,map_mul,conjugate_inverse]

lemma commutator_norm (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    ‖U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T‖=
      ‖T*U.conjStarAlgEquiv a-U.conjStarAlgEquiv a*T‖ := by
  have : StarHomClass ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
      (H →L[ℂ] H) (K →L[ℂ] K) :=
    ⟨fun equivalence => equivalence.map_star'⟩
  rw [←conjugate_commutator,
    StarAlgEquiv.norm_map (A := H →L[ℂ] H) (B := K →L[ℂ] K) U.conjStarAlgEquiv]

lemma commutes_iff (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    U.symm.conjStarAlgEquiv T*a=a*U.symm.conjStarAlgEquiv T ↔
      T*U.conjStarAlgEquiv a=U.conjStarAlgEquiv a*T := by
  constructor
  · intro h
    simpa only [map_mul,conjugate_inverse] using congrArg U.conjStarAlgEquiv h
  · intro h
    apply U.conjStarAlgEquiv.injective
    change U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T*a)=
      U.conjStarAlgEquiv (a*U.symm.conjStarAlgEquiv T)
    simpa only [map_mul,conjugate_inverse] using h

lemma commutator_norm_of_conjugates (T b : K →L[ℂ] K) (a : H →L[ℂ] H)
    (h : U.conjStarAlgEquiv a=b) :
    ‖U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T‖=‖T*b-b*T‖ := by
  rw [commutator_norm,h]

lemma commutes_of_conjugates (T b : K →L[ℂ] K) (a : H →L[ℂ] H)
    (h : U.conjStarAlgEquiv a=b) (hc : T*b=b*T) :
    U.symm.conjStarAlgEquiv T*a=a*U.symm.conjStarAlgEquiv T := by
  rw [commutes_iff,h]
  exact hc

end Kadison.UnitaryTransport

end

end
end

end OAI
