import Mathlib
import OAI.Analysis.Commutator.AmplifiedTowerStage
import OAI.Analysis.Commutator.MatrixTensorRange

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance amplifiedTowerGeometryIndexDecidableEq : DecidableEq ι := Classical.decEq ι

variable (E : ℕ → MatrixTower.Stage M)

lemma amplifiedStage_monotone (hE : Monotone (fun n => (E n).hom.range)) :
    Monotone (fun n => (amplifiedStage ι i₀ M (E n)).hom.range) := by
  intro n m h
  apply MatrixTensor.range_le (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp (E n).hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x ((E n).hom y))
    ((amplifiedStage ι i₀ M (E m)).hom.range)
  · rintro a ⟨b,rfl⟩
    exact amplifiedStage_scalar ι i₀ M (E m) b
  · rintro a ⟨b,rfl⟩
    obtain ⟨c,hc⟩ := hE h (show (E n).hom b∈(E n).hom.range from ⟨b,rfl⟩)
    change diagonalHom ι i₀ M ((E n).hom b)∈_
    rw [←hc]
    exact amplifiedStage_diagonal ι i₀ M (E m) c

lemma amplifiedStage_irreducible
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ c : ℂ,a=c • (1:M))
    (Z : matrixVonNeumann ι i₀ M)
    (hZ : ∀ n b,(amplifiedStage ι i₀ M (E n)).hom b*Z=Z*(amplifiedStage ι i₀ M (E n)).hom b) :
    ∃ c : ℂ,Z=algebraMap ℂ (matrixVonNeumann ι i₀ M) c := by
  have hs (i j : ι) : matrixUnit (H:=H) ι i j*(Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*matrixUnit ι i j := by
    obtain ⟨b,hb⟩ := amplifiedStage_scalar ι i₀ M (E 0) (Matrix.single i j 1)
    change (amplifiedStage ι i₀ M (E 0)).hom b=scalarMatrixHom ι i₀ M (Matrix.single i j 1) at hb
    have hh := hZ 0 b
    rw [hb] at hh
    have hh' := congrArg (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype hh
    change (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
      (scalarMatrixHom ι i₀ M (Matrix.single i j 1):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) at hh'
    rw [scalarMatrixHom_single] at hh'
    exact hh' 
  let a : M := ⟨entry ι (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i₀ i₀,
    (mem_matrixVonNeumann ι i₀ M Z).mp Z.property i₀ i₀⟩
  have ha (n : ℕ) (b : Matrix (E n).I (E n).I ℂ) : (E n).hom b*a=a*(E n).hom b := by
    obtain ⟨c,hc⟩ := amplifiedStage_diagonal ι i₀ M (E n) b
    apply Subtype.ext
    apply entry_commutes ι (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    change (amplifiedStage ι i₀ M (E n)).hom c=diagonalHom ι i₀ M ((E n).hom b) at hc
    have hh := hZ n c
    rw [hc] at hh
    exact congrArg (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype hh
  obtain ⟨c,hc⟩ := hirr a ha
  refine ⟨c,?_⟩
  apply Subtype.ext
  have hdiag := diagonal_of_matrixUnits ι i₀ (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) hs
  change (Z:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=c • 1
  rw [hdiag]
  change diagonal (H:=H) ι (a:H →L[ℂ] H)=_
  rw [hc]
  change diagonal (H:=H) ι (c • 1)=c • 1
  rw [map_smul,map_one]

lemma amplifiedStage_in_relative (R : VonNeumannAlgebra H)
    (hE : ∀ n a,((E n).hom a:H →L[ℂ] H)∈R) (n : ℕ)
    (a : Matrix (amplifiedStage ι i₀ M (E n)).I (amplifiedStage ι i₀ M (E n)).I ℂ) :
    ((amplifiedStage ι i₀ M (E n)).hom a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)∈matrixVonNeumann ι i₀ R := by
  let S : StarSubalgebra ℂ (matrixVonNeumann ι i₀ M) :=
    (matrixVonNeumann ι i₀ R).toStarSubalgebra.comap (matrixVonNeumann ι i₀ M).toStarSubalgebra.subtype
  apply MatrixTensor.range_le (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp (E n).hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x ((E n).hom y)) S _ _ ⟨a,rfl⟩
  · rintro b ⟨x,rfl⟩
    change (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)∈matrixVonNeumann ι i₀ R
    rw [scalarMatrixHom_coe]
    apply (matrixVonNeumann ι i₀ R).sum_mem
    intro i _
    apply (matrixVonNeumann ι i₀ R).sum_mem
    intro j _
    exact (matrixVonNeumann ι i₀ R).smul_mem (matrixUnit_mem ι i₀ R i j) _
  · rintro b ⟨x,rfl⟩
    exact diagonal_mem_matrixVonNeumann ι i₀ R (hE n x)

lemma amplifiedStage_size (n : ℕ) :
    Fintype.card (amplifiedStage ι i₀ M (E n)).I=Fintype.card ι*Fintype.card (E n).I :=
  Fintype.card_prod ι (E n).I

end Kadison.OperatorAmplification

end

end
end

end OAI
