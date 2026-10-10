import Mathlib
import OAI.Analysis.Commutator.StableUniversalAssembly

namespace OAI

noncomputable section

noncomputable section

namespace Kadison

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem uniform_commutant_approximation (M : VonNeumannAlgebra H) (G : H →L[ℂ] H) :
    ∃ T : H →L[ℂ] H, T∈M.commutant ∧
      ‖G-T‖≤9368*commutatorSeminorm M G := by
  apply WOTDistance.exists_commutant_approximation M G
    (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M G))
  intro n T hT
  cases n with
  | zero =>
    have hT0 : T=0 := Subsingleton.elim _ _
    simp [hT0]
  | succ n =>
    have he : matrixOperator (n+1) (entry (Fin (n+1)) T)=T := by
      ext x i
      exact (matrixOperator_apply (n+1) (entry (Fin (n+1)) T) x i).trans
        (apply_eq_sum_entries (Fin (n+1)) T x i).symm
    have hd : diagonal (H:=H) (Fin (n+1)) G=diagonalAmplification (n+1) G := rfl
    rw [hd]
    simpa only [he] using
      CentralSpectral.universal_bound M G (n+1) (Nat.succ_pos n) (entry (Fin (n+1)) T) hT

end Kadison
end
end

end OAI
