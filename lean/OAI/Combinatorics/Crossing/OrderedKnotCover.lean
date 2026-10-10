import OAI.Combinatorics.Crossing.NormalizedPolygonalDrawing
import Mathlib.Data.Finset.Max

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem ordered_knots_cover {k : ℕ} (hk : 0 < k) (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (h0 : t 0=0) (h1 : t (Fin.last k)=1) (u : unitInterval) :
    ∃ i : Fin k, t i.castSucc ≤ u ∧ u ≤ t i.succ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (k+1) => t i ≤ u)
  have hS : S.Nonempty := ⟨0,by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,h0]; exact u.property.1⟩
  let j := S.max' hS
  have hj : t j ≤ u := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  by_cases hjlast : j.val=k
  · let i : Fin k := ⟨k-1,by omega⟩
    have hjl : j=Fin.last k := Fin.ext hjlast
    have hi : i.succ=Fin.last k := by apply Fin.ext; change k-1+1=k; omega
    have hu : u=1 := le_antisymm u.property.2 (by simpa only [hjl,h1] using hj)
    refine ⟨i,?_,?_⟩
    · rw [hu, ← h1]
      exact (ht (Fin.castSucc_lt_last i)).le
    · rw [hi,h1,hu]
  · have hjk : j.val < k := by have hh := j.isLt; omega
    let i : Fin k := ⟨j.val,hjk⟩
    have hij : i.castSucc=j := Fin.ext rfl
    refine ⟨i,by rw [hij]; exact hj,?_⟩
    by_contra hu
    have hmem : i.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(lt_of_not_ge hu).le⟩
    have hh : i.succ ≤ j := Finset.le_max' S i.succ hmem
    change j.val+1 ≤ j.val at hh
    omega

theorem PolygonalParametrization.knot_cover {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (u : unitInterval) :
    ∃ i : Fin P.pieces, P.knot i.castSucc ≤ u ∧ u ≤ P.knot i.succ :=
  ordered_knots_cover P.pieces_pos P.knot P.increasing P.first P.last u

end Zarankiewicz

end

end OAI
