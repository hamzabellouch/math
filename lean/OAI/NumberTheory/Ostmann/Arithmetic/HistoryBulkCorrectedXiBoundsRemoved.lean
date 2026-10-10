import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern

private theorem sum_filter_map {α : Type*} (xs : List α) (p : α → Bool) (f : α → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [hp,ih]

theorem actual_history_U_window (b k l : ℕ) (G : ℝ) (center : ℕ → ℝ)
    (h : History l)
    (hm : Template.Matches (Template.current (Template.initial (2*b) k) l) h.root.small)
    (x : Key h → ℝ) (hx : SourceDomain b k G center h x) :
    |Real.log (((diagonalUKeys h (l+1)).map x).prod) -
      (2:ℝ)^l*removedCenter b k l center| ≤ removedWidth k l := by
  let T := Template.current (Template.initial (2*b) k) l
  have hsum (F : SlotRole → ℕ → ℝ) :
      sourceSum (fun q => F q.role q.origin) (Template.extracted (l+1) T) =
        ∑i : Fin h.root.small.length, if (h.root.small.get i).role = .compensation (l+1)
          then F (h.root.small.get i).role (h.root.small.get i).origin else 0 := by
    rw [matches_metadata_fin_sum hm (fun r o => if r = .compensation (l+1) then F r o else 0)]
    simpa only [sourceSum,Template.extracted,decide_eq_true_eq] using
      sum_filter_map T (fun q => decide (q.role = .compensation (l+1))) (fun q => F q.role q.origin)
  have hC := hsum (fun r o => if r = .bulk then 0 else center o)
  have hN := hsum (fun r _ => if r = .bulk then (0:ℝ) else 1)
  have hcenter : sourceSum (fixedCenter center) (Template.extracted (l+1) T) =
      (2:ℝ)^l*removedCenter b k l center := sourceSum_current_filter (fixedCenter center) _ _ l
  have hcount := fixedCount_current_filter_le
    (fun q => decide (q.role = .compensation (l+1))) (2*b) k l
  change sourceSum fixedCount (Template.extracted (l+1) T) ≤ removedWidth k l at hcount
  rw [←hcenter]
  change |Real.log (((diagonalUKeys h (l+1)).map x).prod) -
    sourceSum (fun q => if q.role = .bulk then 0 else center q.origin) (Template.extracted (l+1) T)| ≤ _
  rw [hC]
  have he : |Real.log (((diagonalUKeys h (l+1)).map x).prod) -
      ∑i : Fin h.root.small.length, if (h.root.small.get i).role = .compensation (l+1)
      then (if (h.root.small.get i).role = .bulk then 0 else center (h.root.small.get i).origin) else 0| ≤
      sourceSum fixedCount (Template.extracted (l+1) T) := by
    change _ ≤ sourceSum (fun q => if q.role = .bulk then (0:ℝ) else 1) _
    rw [hN]
    rw [diagonalUKeys,log_role_product h _ x hx.positive]
    simp only [decide_eq_true_eq]
    rw [←Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hr : (h.root.small.get i).role = .compensation (l+1)
    · have hb : (h.root.small.get i).role ≠ .bulk := by rw [hr]; simp
      simpa only [ite_eq_left hr,ite_eq_right hb] using
        hx.source (.inr (.inl i)) (h.root.small.get i) rfl hb
    · simp only [ite_eq_right hr,sub_self,abs_zero,le_refl]
  exact he.trans hcount

theorem selected_paired_U_window {d : Decomposition} {Bs BD Bz : ℝ} {k₀ l : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (hl : l < k₀) (h k : History l)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (x : PairKey h k → ℝ)
    (hx : SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter
      (C.cells.center (bulkSize k₀ L/2)) k (fun i => x (rightMap h k i))) :
    |Real.log (((pairedDiagonalUKeys h k (l+1)).map x).prod) -
      C.compensationLogScale l| ≤ nominalRemovedWidth k₀ l := by
  apply removed_window_normalize (bulkSize k₀ L/2) k₀ l hl _
    (nominalWeight k₀ (nominalJ Bs BD Bz k₀ L C.blockBase C.giantCenter C.spectatorBin)
      (stepGap BD Bz k₀ L)) (C.cells.center (bulkSize k₀ L/2)) _
    (C.type_frequency_center_error _)
  simpa only [pairedDiagonalUKeys,List.map_map,Function.comp_def] using
    actual_history_U_window (bulkSize k₀ L/2) k₀ l C.giantCenter _ k (root_matches hk) _ hx

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
