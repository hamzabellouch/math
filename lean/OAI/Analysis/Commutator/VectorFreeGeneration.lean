import Mathlib
import OAI.Analysis.Commutator.GNSCornerTransport
import OAI.Analysis.Commutator.NormalGNSClosure
import OAI.Analysis.Commutator.NormalFreeCorner

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

abbrev inclusion (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    D →⋆ₐ[ℂ] M := StarSubalgebra.inclusion hDM

lemma inclusion_injective (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    Function.Injective (inclusion M D hDM) := StarSubalgebra.inclusion_injective hDM

lemma factorTrace_inclusion (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
      (inclusion_injective M D hDM)=subalgebraTrace D ξ := by
  ext a
  rfl

lemma factorTrace_inclusion_normal (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    NormalGNS.BoundedWOTContinuous D
      (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
        (inclusion_injective M D hDM)) := by
  rw [factorTrace_inclusion]
  exact subalgebraTrace_normal D ξ

theorem gns_generation (R : Bool → StarSubalgebra ℂ M)
    (hgen : ∀ a : M,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (((iSup R).map M.toStarSubalgebra.subtype) : Set (H →L[ℂ] H)))) (a : M) :
    (subalgebraTrace M ξ).gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (generatedOperators (vectorState M ξ hfaith hone) R : Set _)) := by
  let t := vectorState M ξ hfaith hone
  let S := (iSup R).map M.toStarSubalgebra.subtype
  let N := ambientVonNeumann t R
  have hSM : S≤M.toStarSubalgebra := by
    rintro x ⟨b,_,rfl⟩
    exact b.property
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈S) :
      (subalgebraTrace M ξ).gnsStarAlgHom b∈N := by
    obtain ⟨c,hc,hcb⟩ := hb
    have he : c=b := Subtype.ext hcb
    subst c
    exact (mem_ambientOperators t R).mpr (Set.subset_centralizer_centralizer ⟨b,hc,rfl⟩)
  exact (mem_ambientOperators t R).mp
    (NormalGNS.image_bicommutant_general M (subalgebraTrace M ξ)
      (subalgebraTrace_normal M ξ) S hSM N hSN a (hgen a))

end Kadison.VectorGNS

end

end
end

end OAI
