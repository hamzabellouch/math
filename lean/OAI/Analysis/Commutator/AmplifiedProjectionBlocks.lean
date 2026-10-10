import Mathlib
import OAI.Analysis.Commutator.AmplifiedStrongLimit
import OAI.Analysis.Commutator.OperatorAmplification
import OAI.Analysis.Commutator.ProjectionBlocks

namespace OAI

noncomputable section

noncomputable section

open Filter

open scoped InnerProductSpace ComplexOrder Topology BigOperators

namespace Kadison.ProjectionBlocks

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : ι → H →L[ℂ] H) (hp : ∀ i,IsStarProjection (P i))
    (ho : ∀ i j,i≠j → P i*P j=0) (h : ℕ)

include hp in
lemma diagonal_projection (i : ι) : IsStarProjection (diagonalAmplification h (P i)) := by
  change IsStarProjection (OperatorAmplification.diagonal (H:=H) (Fin h) (P i))
  exact (hp i).map (OperatorAmplification.diagonal (H:=H) (Fin h))

include ho in
lemma diagonal_orthogonal (i j : ι) (hij : i≠j) :
    diagonalAmplification h (P i)*diagonalAmplification h (P j)=0 := by
  change OperatorAmplification.diagonal (H:=H) (Fin h) (P i)*OperatorAmplification.diagonal (H:=H) (Fin h) (P j)=0
  rw [←map_mul,ho i j hij,map_zero]

lemma finiteSum_diagonal (s : Finset ι) :
    finiteSum (fun i => diagonalAmplification h (P i)) s=diagonalAmplification h (finiteSum P s) := by
  change (∑ i∈s,OperatorAmplification.diagonal (H:=H) (Fin h) (P i))=
    OperatorAmplification.diagonal (H:=H) (Fin h) (∑ i∈s,P i)
  exact (map_sum _ _ _).symm

include hp ho in
lemma diagonal_space_projection :
    (space (fun i => diagonalAmplification h (P i))).starProjection=
      diagonalAmplification h (space P).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have h₁ := finiteSum_tendsto (fun i => diagonalAmplification h (P i))
    (diagonal_projection P hp h) (diagonal_orthogonal P ho h) x
  have h₂ := StrongContractionLimit.diagonal_tendsto (finiteSum P) (space P).starProjection
    (finiteSum_tendsto P hp ho) h x
  simp only [←finiteSum_diagonal P h] at h₂
  exact tendsto_nhds_unique h₁ h₂

include hp ho in
lemma diagonal_full (hfull : (space P).starProjection=1) :
    (space (fun i => diagonalAmplification h (P i))).starProjection=1 := by
  rw [diagonal_space_projection P hp ho h,hfull]
  exact map_one (OperatorAmplification.diagonal (H:=H) (Fin h))

end Kadison.ProjectionBlocks
end
end

end OAI
