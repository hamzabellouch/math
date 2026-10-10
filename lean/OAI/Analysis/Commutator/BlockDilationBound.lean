import Mathlib
import OAI.Analysis.Commutator.BalancedSymmetry
import OAI.Analysis.Commutator.MatrixEntryWOT

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

local instance blockDilationIndexDecidableEq : DecidableEq ι := Classical.decEq ι

local instance blockDilationFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

lemma entry_starHom_matrixRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (i j : ι) :
    entry ι (CyclicColumns.matrixRepresentation ρ X) i j=ρ (X i j) := by
  ext x
  change CyclicColumns.matrixAction (fun i j => ρ (X i j)) (single ι j x) i=ρ (X i j) x
  simp only [CyclicColumns.matrixAction_apply, single_apply]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma entry_diagonal_commutator (T : H →L[ℂ] H)
    (X : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    entry ι (diagonal (H:=H) ι T*X-X*diagonal (H:=H) ι T) i j=
      T*entry ι X i j-entry ι X i j*T := by
  ext v
  simp [entry_apply,mul_apply_eq_comp,diagonal_single]

lemma commutator_entry_norm_le (T : H →L[ℂ] H)
    (X : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    ‖T*entry ι X i j-entry ι X i j*T‖≤
      ‖diagonal (H:=H) ι T*X-X*diagonal (H:=H) ι T‖ := by
  rw [←entry_diagonal_commutator]
  exact norm_entry_le ι _ i j

theorem balanced_symmetry_commutator_dominates
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H) (X : A) :
    ‖Y*ρ X-ρ X*Y‖≤
      ‖diagonal (H:=H) (Fin 2) Y*
          CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)-
        CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)*
          diagonal (H:=H) (Fin 2) Y‖ := by
  have he : entry (Fin 2) (CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)) 0 1=ρ X := by
    rw [entry_starHom_matrixRepresentation]
    rfl
  simpa only [he] using commutator_entry_norm_le Y
    (CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)) (0:Fin 2) 1

end Kadison.OperatorAmplification

end

end
end

end OAI
