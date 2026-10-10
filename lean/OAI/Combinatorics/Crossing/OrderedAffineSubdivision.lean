import OAI.Combinatorics.Crossing.AffineIntervalRestriction
import OAI.Combinatorics.Crossing.SortedMarkedParameters
import OAI.Combinatorics.Crossing.IntervalSegmentStrict
import OAI.Combinatorics.Crossing.PolygonalParametrization

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

theorem HasFiniteAffineCover.nonempty_polygonalParametrization {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) : Nonempty (PolygonalParametrization γ) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 (S.image Prod.fst ∪ S.image Prod.snd))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=?_}⟩
  intro i u
  let mid : unitInterval := ⟨1/2,by norm_num⟩
  let z := intervalSegment (t i.castSucc) (t i.succ) mid
  have hz : t i.castSucc < z ∧ z < t i.succ :=
    intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
      constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
  obtain ⟨ab,hab,ha,hb⟩ := hScov z
  have hlo : ab.1 ≤ t i.castSucc := by
    by_contra hn
    obtain ⟨j,hj⟩ := hleft ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
  have hhi : t i.succ ≤ ab.2 := by
    by_contra hn
    obtain ⟨j,hj⟩ := hright ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
  have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
  exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
    (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u

end Zarankiewicz

end

end OAI
