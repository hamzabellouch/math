import Mathlib
import OAI.Analysis.Commutator.DiagonalVonNeumann
import OAI.Analysis.Commutator.CyclicSpatialImplementation

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

open CyclicColumns CyclicSpatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

local instance matrixAlgebraDensityDecidableEq : DecidableEq ι := Classical.decEq ι

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

local instance : PartialOrder S := CStarAlgebra.spectralOrder S

local instance : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S

def fullMatrixAlgebra : StarSubalgebra ℂ (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :=
  (matrixRepresentation (ι:=ι) S.subtype).range

lemma fullMatrixAlgebra_closed : IsClosed (fullMatrixAlgebra ι S :
    Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)) := by
  exact (NonUnitalStarAlgHom.isometry (matrixRepresentation (ι:=ι) S.subtype)
    (matrixRepresentation_injective S.subtype Subtype.val_injective)).isClosedEmbedding.isClosed_range

lemma entry_represented (X : CStarMatrix ι ι S) (i j : ι) :
    entry ι (matrixRepresentation S.subtype X) i j=(X i j:H →L[ℂ] H) := by
  ext x
  simp [entry_apply,represented_matrix_apply,single_apply,apply_ite]

lemma mem_fullMatrixAlgebra_iff (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈fullMatrixAlgebra ι S ↔ ∀ i j, entry ι T i j∈S := by
  constructor
  · rintro ⟨X,rfl⟩ i j
    change entry ι (matrixRepresentation S.subtype X) i j ∈ S
    rw [entry_represented]
    exact (X i j).property
  · intro h
    let X : CStarMatrix ι ι S := CStarMatrix.ofMatrix (fun i j => ⟨entry ι T i j,h i j⟩)
    refine ⟨X,?_⟩
    change CyclicColumns.matrixAction (entry ι T)=T
    exact reconstruct ι T

lemma diagonal_mem_fullMatrixAlgebra {a : H →L[ℂ] H} (ha : a∈S) :
    diagonal (H:=H) ι a∈fullMatrixAlgebra ι S := by
  rw [mem_fullMatrixAlgebra_iff]
  intro i j
  have he : entry ι (diagonal (H:=H) ι a) i j=if i=j then a else 0 := by
    ext x
    by_cases hij : i=j <;> simp [entry_apply,diagonal_apply,single_apply,hij]
  rw [he]
  split_ifs <;> simp_all

lemma matrixUnit_mem_fullMatrixAlgebra (i j : ι) :
    matrixUnit (H:=H) ι i j∈fullMatrixAlgebra ι S := by
  rw [mem_fullMatrixAlgebra_iff]
  intro k l
  have he : entry ι (matrixUnit (H:=H) ι i j) k l=if k=i ∧ j=l then 1 else 0 := by
    ext x
    by_cases hki : k=i <;> by_cases hjl : j=l <;>
      simp [entry_apply,matrixUnit_apply,single_apply,hki,hjl]
  rw [he]
  split_ifs <;> simp

lemma bicommutant_fullMatrix_of_entries (i₀ : ι)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hT : ∀ i j, entry ι T i j∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    T∈Set.centralizer (Set.centralizer (fullMatrixAlgebra ι S :
      Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι))) := by
  intro R hR
  have hU : ∀ i j, matrixUnit ι i j*R=R*matrixUnit ι i j :=
    fun i j => hR _ (matrixUnit_mem_fullMatrixAlgebra ι S i j)
  have he := diagonal_of_matrixUnits ι i₀ R hU
  let a := entry ι R i₀ i₀
  have ha : a∈Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro b hb
    exact entry_commutes ι R b (hR _ (diagonal_mem_fullMatrixAlgebra ι S hb)) i₀ i₀
  rw [he]
  exact commutes_of_entries ι T a (fun i j => hT i j a ha)

end Kadison.OperatorAmplification

end

end
end

end OAI
