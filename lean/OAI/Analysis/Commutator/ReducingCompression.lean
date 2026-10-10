import Mathlib
import OAI.Analysis.Commutator.FiniteHankel
import OAI.Analysis.Commutator.ReducingRepresentation

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

lemma inclusion_intertwines (a : A) : (σ a).comp K.subtypeL=
    K.subtypeL.comp (restrict σ K hinv a) := rfl

lemma projection_intertwines (a : A) : K.orthogonalProjectionOnto.comp (σ a)=
    (restrict σ K hinv a).comp K.orthogonalProjectionOnto := by
  have h := congrArg (fun T : K →L[ℂ] H => T.adjoint) (inclusion_intertwines σ K hinv (star a))
  simpa only [adjoint_comp,Submodule.adjoint_subtypeL,map_star,star_eq_adjoint,adjoint_adjoint] using h

def compression (S : H →L[ℂ] H) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (S.comp K.subtypeL)

lemma compression_eq (S : H →L[ℂ] H) : compression K S=FreeCorner.compress K.subtypeₗᵢ S := by
  change K.orthogonalProjectionOnto.comp (S.comp K.subtypeL)=
    (K.subtypeL.adjoint.comp S).comp K.subtypeL
  rw [Submodule.adjoint_subtypeL]
  rfl

lemma norm_compression_le (S : H →L[ℂ] H) : ‖compression K S‖≤‖S‖ := by
  rw [compression_eq]
  exact FreeCorner.norm_compress_le _ S

lemma compression_left (S : H →L[ℂ] H) (a : A) :
    compression K (σ a*S)=restrict σ K hinv a*compression K S := by
  simp only [compression,mul_def,←comp_assoc]
  rw [projection_intertwines σ K hinv]

lemma compression_right (S : H →L[ℂ] H) (a : A) :
    compression K (S*σ a)=compression K S*restrict σ K hinv a := by
  simp only [compression,mul_def,comp_assoc]
  rw [inclusion_intertwines σ K hinv]

omit [CompleteSpace H] in
lemma compression_sub (S T : H →L[ℂ] H) : compression K (S-T)=compression K S-compression K T := by
  simp only [compression,comp_sub,sub_comp]

lemma compression_commutator (S : H →L[ℂ] H) (a : A) :
    compression K (S*σ a-σ a*S)=
      compression K S*restrict σ K hinv a-restrict σ K hinv a*compression K S := by
  rw [compression_sub,compression_left σ K hinv,compression_right σ K hinv]

lemma norm_commutator_compression_le (S : H →L[ℂ] H) (a : A) :
    ‖compression K S*restrict σ K hinv a-restrict σ K hinv a*compression K S‖≤‖S*σ a-σ a*S‖ := by
  rw [←compression_commutator σ K hinv]
  exact norm_compression_le K _

end Kadison.ReducingRepresentation

end

end
end

end OAI
