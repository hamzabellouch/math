import OAI.Combinatorics.Crossing.MatrixRankSum
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem matrix_rank_sum_bound_indexed {κ : Type*} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (X Y : Fin m → Matrix κ κ ℝ) (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2*axisPairs m*Fintype.card κ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank := by
  let e := Fintype.equivFin κ
  let R := Matrix.reindexRingEquiv ℝ e
  have hunit : ∀ i, IsUnit (R (X i)-R (Y i)) := by
    intro i
    rw [← map_sub]
    exact (hdiag i).map R.toMonoidHom
  have hrank (i j : Fin m) : (R (X i)-R (Y j)).rank=(X i-Y j).rank := by
    rw [← map_sub]
    exact Matrix.rank_reindex e e (X i-Y j)
  have h := matrix_rank_sum_bound m (Fintype.card κ) (fun i => R (X i)) (fun i => R (Y i)) hunit
  simpa only [offDiagonalRankSum,hrank] using h

theorem matrix_rank_sum_bound_product (m s : ℕ)
    (X Y : Fin m → Matrix (Fin s × Fin s) (Fin s × Fin s) ℝ)
    (hdiag : ∀ i, IsUnit (X i-Y i)) :
    2*axisPairs m*(s*s) ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (X i-Y j).rank := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using matrix_rank_sum_bound_indexed m X Y hdiag

end Zarankiewicz

end

end OAI
