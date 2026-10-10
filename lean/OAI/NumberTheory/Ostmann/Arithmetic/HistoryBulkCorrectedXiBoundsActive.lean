import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern
open HistoryPairBulkCoordinates HistoryActiveCoordinates PrimeCellFreezing
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem bulk_sourceDomains {b k₀ : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h k : History l) (hs : h.Supported V outside) (e : RootMatching h k)
    (background : PairKey h k → ℝ)
    (hh : SourceDomain b k₀ G center h (fun i => background (leftMap h k i)))
    (hk : SourceDomain b k₀ G center k (fun i => background (rightMap h k i)))
    (x : bulkCoordinates h k → ℝ) (hx : ∀i, 0 < x i) :
    SourceDomain b k₀ G center h
      (fun i => insert (bulkCoordinates h k) background x (leftMap h k i)) ∧
    SourceDomain b k₀ G center k
      (fun i => insert (bulkCoordinates h k) background x (rightMap h k i)) := by
  let z : bulkCoordinates h k → ℝ := fun i => Real.log (x i)
  have hz : z ∈ logRectangle z z := fun i _ => ⟨le_rfl,le_rfl⟩
  have hexp : (fun i => Real.exp (z i)) = x := by
    funext i
    exact Real.exp_log (hx i)
  constructor
  · rw [←hexp]
    apply sourceDomain_insert_exp b k₀ G center h (leftMap h k) _ background z z hh _ _ z hz
    · intro i q hiq hq hm
      rcases i with a | i | i
      · cases hiq
      · have he : h.root.small.get i = q := Option.some.inj hiq
        exact (left_nonbulk_not_mem h k hs i (he ▸ hq) hm).elim
      · exact (left_internal_not_mem h k i hm).elim
    · intro a hm
      exact (left_giant_not_mem h k a hm).elim
  · rw [←hexp]
    apply sourceDomain_insert_exp b k₀ G center k (rightMap h k) _ background z z hk _ _ z hz
    · intro i q hiq hq hm
      rcases i with a | i | i
      · cases hiq
      · have he : k.root.small.get i = q := Option.some.inj hiq
        exact (right_nonbulk_not_mem h k hs e i (he ▸ hq) hm).elim
      · exact (right_internal_not_mem h k i hm).elim
    · intro a hm
      exact (right_giant_not_mem h k a hm).elim

theorem bulk_U_product (h k : History l) (hs : h.Supported V outside)
    (e : RootMatching h k) (j : ℕ) (background : PairKey h k → ℝ)
    (x : bulkCoordinates h k → ℝ) :
    ((pairedDiagonalUKeys h k j).map (insert (bulkCoordinates h k) background x)).prod =
      ((pairedDiagonalUKeys h k j).map background).prod := by
  congr 1
  apply List.map_congr_left
  intro a ha
  change a ∈ (diagonalUKeys k j).map (rightMap h k) at ha
  obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp ha
  change key ∈ ((List.finRange k.root.small.length).filter
    (fun i => decide ((k.root.small.get i).role = .compensation j))).map
      (fun i => Sum.inr (Sum.inl i)) at hkey
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hkey
  have hp := (List.mem_filter.mp hi).2
  have hr : (k.root.small.get i).role = .compensation j := by simpa using hp
  have hn := right_nonbulk_not_mem h k hs e i (by rw [hr]; simp)
  simp only [HistoryActiveCoordinates.insert,dite_eq_right hn]

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
