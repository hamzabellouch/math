import Mathlib
import OAI.Analysis.Commutator.DiagonalVonNeumann
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (i₀ : ι)

def matrixVonNeumann (M : VonNeumannAlgebra H) : VonNeumannAlgebra (SumSpace (H:=H) ι) :=
  (diagonalVonNeumann ι i₀ M.commutant).commutant

lemma mem_matrixVonNeumann (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈matrixVonNeumann ι i₀ M ↔ ∀ i j,entry ι T i j∈M := by
  change T∈(diagonalVonNeumann ι i₀ M.commutant).commutant ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  constructor
  · intro h i j
    rw [←SetLike.mem_coe,←M.centralizer_centralizer]
    intro b hb
    exact entry_commutes ι T b (h (diagonal (H:=H) ι b) ⟨b,VonNeumannAlgebra.mem_commutant_iff.mpr hb,rfl⟩) i j
  · intro h
    rintro _ ⟨b,hb,rfl⟩
    apply commutes_of_entries ι T b
    intro i j
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hb) _ (h i j)).symm

lemma matrixUnit_mem (M : VonNeumannAlgebra H) (i j : ι) :
    matrixUnit (H:=H) ι i j∈matrixVonNeumann ι i₀ M := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  rintro _ ⟨b,_,rfl⟩
  exact (matrixUnit_commutes ι i j b).symm

lemma diagonal_mem_matrixVonNeumann (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a∈M) :
    diagonal (H:=H) ι a∈matrixVonNeumann ι i₀ M := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  rintro _ ⟨b,hb,rfl⟩
  exact (map_mul (diagonal (H:=H) ι) b a).symm.trans
    ((congrArg (diagonal (H:=H) ι) ((VonNeumannAlgebra.mem_commutant_iff.mp hb) a ha).symm).trans (map_mul (diagonal (H:=H) ι) a b))

lemma matrix_representation_mem (M : VonNeumannAlgebra H) (X : CStarMatrix ι ι M) :
    CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X∈matrixVonNeumann ι i₀ M := by
  rw [mem_matrixVonNeumann]
  intro i j
  have he : entry ι (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X) i j=
      (X i j:H →L[ℂ] H) := by
    ext x
    simp only [entry_apply,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
      StarAlgHom.coe_mk]
    simp [apply_ite]
    rfl
  rw [he]
  exact (X i j).property

lemma matrixVonNeumann_is_range (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (hT : T∈matrixVonNeumann ι i₀ M) :
    ∃ X : CStarMatrix ι ι M,CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X=T := by
  have h := (mem_matrixVonNeumann ι i₀ M T).mp hT
  let X : CStarMatrix ι ι M := CStarMatrix.ofMatrix (fun i j => ⟨entry ι T i j,h i j⟩)
  exact ⟨X,reconstruct ι T⟩

lemma factor_matrixVonNeumann (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M) :
    FactorCorner.IsFactor (matrixVonNeumann ι i₀ M) := by
  intro Z hZ hc
  have he : Z=diagonal (H:=H) ι (entry ι Z i₀ i₀) :=
    diagonal_of_matrixUnits ι i₀ Z (fun i j => hc _ (matrixUnit_mem ι i₀ M i j))
  have ha := (mem_matrixVonNeumann ι i₀ M Z).mp hZ i₀ i₀
  have hca : entry ι Z i₀ i₀∈Set.centralizer (M:Set (H →L[ℂ] H)) := by
    intro a ha
    exact entry_commutes ι Z a (hc _ (diagonal_mem_matrixVonNeumann ι i₀ M ha)) i₀ i₀
  obtain ⟨c,hc⟩ := hM _ ha hca
  refine ⟨c,?_⟩
  rw [he,hc,map_smul,map_one]

end Kadison.OperatorAmplification

end

end
end

end OAI
