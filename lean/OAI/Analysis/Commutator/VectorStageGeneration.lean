import Mathlib
import OAI.Analysis.Commutator.MatrixStageGNSGeneration
import OAI.Analysis.Commutator.VectorFreeGeneration

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (D : VonNeumannAlgebra H) (ξ : H)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

def GeneratedByStages : Prop := ∀ a : D,(subalgebraTrace D ξ).gnsStarAlgHom a∈
  Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra (subalgebraTrace D ξ) I φ : Set _))

lemma generatedByStages_of_represented
    (hgen : ∀ a : D,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages D I φ : Set (H →L[ℂ] H)))) :
    GeneratedByStages D ξ I φ := fun a =>
  NormalGNS.matrix_stages_gns D (subalgebraTrace D ξ) (subalgebraTrace_normal D ξ) I φ a (hgen a)

variable (M : VonNeumannAlgebra H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)
  (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)

lemma factorTrace_generated (hgen : GeneratedByStages D ξ I φ) :
    ∀ a : D,(factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
      (inclusion_injective M D hDM)).gnsStarAlgHom a∈Set.centralizer (Set.centralizer
        (TracialGNS.stageAlgebra (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
          (inclusion_injective M D hDM)) I φ : Set _)) := by
  rw [factorTrace_inclusion]
  exact hgen

end Kadison.VectorGNS

end

end
end

end OAI
