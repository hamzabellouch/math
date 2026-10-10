import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.ReducingRepresentation

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))

variable (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

lemma project_intertwines (a : A) (x : H) :
    K.orthogonalProjectionOnto (σ a x)=restrict σ K hinv a (K.orthogonalProjectionOnto x) := by
  apply Subtype.ext
  have hm : K.starProjection*σ a=σ a*K.starProjection :=
    projection_commutes_of_invariant K (σ a) (hinv a)
      (by simpa only [←map_star] using hinv (star a))
  exact congrArg (fun T : H →L[ℂ] H => T x) hm

def extendZero (T : K →L[ℂ] F) : H →L[ℂ] F := T.comp K.orthogonalProjectionOnto

omit [CompleteSpace H] [CompleteSpace F] in
@[simp] lemma extendZero_subtype (T : K →L[ℂ] F) (x : K) :
    extendZero (K := K) T (x:H)=T x := by simp [extendZero]

include hinv in
lemma extendZero_intertwines (T : K →L[ℂ] F)
    (hT : ∀ a : A, T.comp (restrict σ K hinv a)=(ρ a).comp T) (a : A) :
    (extendZero (K := K) T).comp (σ a)=(ρ a).comp (extendZero (K := K) T) := by
  ext x
  change T (K.orthogonalProjectionOnto (σ a x))=ρ a (T (K.orthogonalProjectionOnto x))
  rw [project_intertwines σ K hinv]
  exact congrArg (fun L : K →L[ℂ] F => L (K.orthogonalProjectionOnto x)) (hT a)

omit [CompleteSpace H] [CompleteSpace F] in
lemma norm_sub_extendZero_apply_le (G : H →L[ℂ] F) (T : K →L[ℂ] F)
    (δ : ℝ) (hδ : ‖G.comp K.subtypeL-T‖≤δ) (x : K) :
    ‖G (x:H)-extendZero (K := K) T (x:H)‖≤δ*‖(x:H)‖ := by
  rw [extendZero_subtype]
  exact ((G.comp K.subtypeL-T).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hδ (norm_nonneg x))

end Kadison.ReducingRepresentation

end

end
end

end OAI
