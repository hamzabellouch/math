import Mathlib
import OAI.Analysis.Commutator.MatrixVonNeumann

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

lemma matrixVonNeumann_mono {Q M : VonNeumannAlgebra H} (hQM : Q≤M) :
    matrixVonNeumann ι i₀ Q ≤ matrixVonNeumann ι i₀ M := by
  intro X hX
  rw [mem_matrixVonNeumann] at hX ⊢
  exact fun i j => hQM (hX i j)

lemma matrixVonNeumann_irreducible (Q M : VonNeumannAlgebra H)
    (hirred : ∀ z∈M, z∈Set.centralizer (Q:Set (H →L[ℂ] H)) →
      ∃ c : ℂ,z=c • (1 : H →L[ℂ] H))
    (Z : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hZ : Z∈matrixVonNeumann ι i₀ M)
    (hc : Z∈Set.centralizer (matrixVonNeumann ι i₀ Q:Set _)) :
    ∃ c : ℂ,Z=c • (1 : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) := by
  have he : Z=diagonal (H:=H) ι (entry ι Z i₀ i₀) :=
    diagonal_of_matrixUnits ι i₀ Z (fun i j => hc _ (matrixUnit_mem ι i₀ Q i j))
  have ha := (mem_matrixVonNeumann ι i₀ M Z).mp hZ i₀ i₀
  have hca : entry ι Z i₀ i₀∈Set.centralizer (Q:Set (H →L[ℂ] H)) := by
    intro a ha
    exact entry_commutes ι Z a (hc _ (diagonal_mem_matrixVonNeumann ι i₀ Q ha)) i₀ i₀
  obtain ⟨c,hc⟩ := hirred _ ha hca
  refine ⟨c,?_⟩
  rw [he,hc,map_smul,map_one]

lemma diagonal_commutes_matrixVonNeumann (Q : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (hY : Y∈Set.centralizer (Q:Set (H →L[ℂ] H)))
    (X : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hX : X∈matrixVonNeumann ι i₀ Q) :
    diagonal (H:=H) ι Y*X=X*diagonal (H:=H) ι Y := by
  apply commutes_of_entries
  intro i j
  exact (hY _ ((mem_matrixVonNeumann ι i₀ Q X).mp hX i j)).symm

end Kadison.OperatorAmplification

end

end
end

end OAI
