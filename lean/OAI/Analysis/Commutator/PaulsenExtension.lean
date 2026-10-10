import Mathlib
import OAI.Analysis.Commutator.ChoiGNS
import OAI.Analysis.Commutator.CpMapOperations
import OAI.Analysis.Commutator.PaulsenPositive
import OAI.Analysis.Commutator.ArvesonExtension
import OAI.Analysis.Commutator.HilbertMatrixCorner

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.Paulsen

open OperatorSystem OperatorAmplification

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

omit [PartialOrder A] [StarOrderedRing A] in
lemma upper_mem (a : A) : ChoiGNS.entry (0 : Fin 2) 1 a∈system A := by
  exact ⟨0,0,by simp,by simp⟩

theorem exists_unital_extension [Nontrivial A] (f : A →ₗ[ℂ] (H →L[ℂ] H))
    (hf : IsCompletelyContractive f) :
    ∃ Φ : CStarMatrix (Fin 2) (Fin 2) A →CP
        (SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)),
      Φ 1=1 ∧ ∀ a : A,
        (single (Fin 2) 0).adjoint.comp ((Φ (ChoiGNS.entry 0 1 a)).comp (single (Fin 2) 1))=f a := by
  let R := CyclicColumns.matrixRepresentation (ι:=Fin 2) (StarAlgHom.id ℂ (H →L[ℂ] H))
  let Rcp : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) →CP
      (SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)) :=
    { toLinearMap := R.toLinearMap
      map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' R }
  let g := R.toLinearMap.comp (systemMap f)
  have hg : IsCompletelyPositive (system A) g :=
    CpOperations.isCompletelyPositive_comp (system A) (systemMap f)
      (systemMap_completelyPositive f hf) Rcp
  obtain ⟨Φ,hΦ⟩ := exists_extension (system A) one_mem star_mem g hg
  refine ⟨Φ,?_,?_⟩
  · have h := hΦ ⟨1,one_mem⟩
    change Φ 1=R (systemMap f ⟨1,one_mem⟩) at h
    simpa only [systemMap_one,map_one] using h
  · intro a
    rw [hΦ ⟨_,upper_mem a⟩]
    change (single (Fin 2) 0).adjoint.comp
      ((R (systemMap f ⟨_,upper_mem a⟩)).comp (single (Fin 2) 1))=f a
    rw [representation_corner]
    simp

end Kadison.Paulsen

end

end
end

end OAI
