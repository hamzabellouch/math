import OAI.Analysis.Pureness.Stabilization.MatrixSystem
import OAI.Analysis.Pureness.Stabilization.MatrixTrace

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem matrixSuccessor_trace (τ : ExtendedTrace A) (n : ℕ) (a : Positive (FinMatrix A n)) :
    τ.matrixTrace (Fin (n+1)) (Positive.map (matrixSuccessor n) a) = τ.matrixTrace (Fin n) a := by
  rw [ExtendedTrace.matrixTrace_apply, ExtendedTrace.matrixTrace_apply, Fin.sum_univ_castSucc]
  have hlast : Positive.matrixDiagonal (Positive.map (matrixSuccessor n) a) (Fin.last n) = Positive.zero := by
    apply Subtype.ext
    simp [Positive.matrixDiagonal,Positive.map,Positive.zero]
  rw [hlast,τ.map_zero,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  exact matrixSuccessor_apply_castSucc n a.1 i i

theorem matrixInclusion_trace (τ : ExtendedTrace A) {n m : ℕ} (h : n ≤ m)
    (a : Positive (FinMatrix A n)) :
    τ.matrixTrace (Fin m) (Positive.map (matrixInclusion h) a) = τ.matrixTrace (Fin n) a := by
  induction m, h using Nat.le_induction with
  | base =>
    congr 1
    apply Subtype.ext
    exact matrixPad_self n a.1
  | succ m h ih =>
    have he : Positive.map (matrixInclusion (Nat.le.step h)) a =
        Positive.map (matrixSuccessor m) (Positive.map (matrixInclusion h) a) :=
      Subtype.ext (matrixPad_succ h a.1)
    rw [he,matrixSuccessor_trace,ih]

theorem matrixInclusion_rank (τ : ExtendedTrace A) {n m : ℕ} (h : n ≤ m)
    (a : Positive (FinMatrix A n)) :
    (τ.matrixTrace (Fin m)).rank (Positive.map (matrixInclusion h) a) = (τ.matrixTrace (Fin n)).rank a := by
  rw [← ExtendedTrace.rank_pullback]
  have he : (τ.matrixTrace (Fin m)).pullback (matrixInclusion h) = τ.matrixTrace (Fin n) := by
    ext b
    exact matrixInclusion_trace τ h b
  rw [he]
end CuntzTrace

end

end OAI
