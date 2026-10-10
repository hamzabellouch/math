import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNormalize
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern

private theorem sum_filter_map {α : Type*} (xs : List α) (p : α → Bool) (f : α → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [hp,ih]

theorem log_role_product {l : ℕ} (h : History l) (p : SmallSlot → Bool)
    (x : Key h → ℝ) (hx : ∀i, 0 < x i) :
    Real.log (((diagonalRoleKeys h p).map x).prod) =
      ∑i : Fin h.root.small.length, if p (h.root.small.get i) then
        Real.log (x (.inr (.inl i))) else 0 := by
  rw [Real.log_list_prod (by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact (hx i).ne')]
  simp only [diagonalRoleKeys,List.map_map,Function.comp_def]
  rw [sum_filter_map]
  rw [←List.ofFn_eq_map,List.sum_ofFn]

theorem remaining_log_error {l : ℕ} (h : History l) (j : ℕ)
    (T : List SourceSlot) (hm : Template.Matches T h.root.small)
    (center : ℕ → ℝ) (x : Key h → ℝ)
    (hc : ∀i, (h.root.small.get i).role ≠ .bulk →
      |Real.log (x (.inr (.inl i)))-center (h.root.small.get i).origin| ≤ 1) :
    |(∑i : Fin h.root.small.length, if (h.root.small.get i).role ≠ .compensation j
      then Real.log (x (.inr (.inl i))) else 0) -
      bulkLog h.root.small (rootExpr h).small x -
      sourceSum (fixedCenter center) (Template.remainder j T)| ≤
      sourceSum fixedCount (Template.remainder j T) := by
  have hC := matches_metadata_fin_sum hm (fun r o =>
    if r ≠ .compensation j then (if r = .bulk then 0 else center o) else 0)
  have hN := matches_metadata_fin_sum hm (fun r _ =>
    if r ≠ .compensation j then (if r = .bulk then (0:ℝ) else 1) else 0)
  have heC : sourceSum (fixedCenter center) (Template.remainder j T) =
      ∑i : Fin h.root.small.length, if (h.root.small.get i).role ≠ .compensation j
      then (if (h.root.small.get i).role = .bulk then 0 else center (h.root.small.get i).origin) else 0 := by
    rw [hC]
    simpa only [sourceSum,Template.remainder,fixedCenter,decide_eq_true_eq] using
      sum_filter_map T (fun q => decide (q.role ≠ .compensation j)) (fixedCenter center)
  have heN : sourceSum fixedCount (Template.remainder j T) =
      ∑i : Fin h.root.small.length, if (h.root.small.get i).role ≠ .compensation j
      then (if (h.root.small.get i).role = .bulk then (0:ℝ) else 1) else 0 := by
    rw [hN]
    simpa only [sourceSum,Template.remainder,fixedCount,decide_eq_true_eq] using
      sum_filter_map T (fun q => decide (q.role ≠ .compensation j)) fixedCount
  rw [heC,heN]
  simp only [bulkLog,slotSum,rootExpr,Expr.realEval]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hb : (h.root.small.get i).role = .bulk
  · have hr : (h.root.small.get i).role ≠ .compensation j := by rw [hb]; simp
    simp only [ite_eq_left hb,ite_eq_left hr,sub_self,abs_zero,le_refl]
  · by_cases hr : (h.root.small.get i).role = .compensation j
    · simp only [ite_eq_right hb,ite_eq_right (not_not.mpr hr),sub_self,abs_zero,le_refl]
    · simpa only [ite_eq_right hb,ite_eq_left hr,sub_zero] using hc i hb

theorem actual_history_H_window (b s k l : ℕ) (X tb td G : ℝ) (center : ℕ → ℝ)
    {V : ℕ → ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hm : Template.Matches (Template.current (Template.initial (2*b) k) l) h.root.small)
    (x : Key h → ℝ) (hx : SourceDomain b k G center h x)
    (hne : actualRealHistoryScalar b s X tb td G outside h hs x ≠ 0) :
    |Real.log (((diagonalHKeys h (l+1)).map x).prod) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l := by
  have hb := inherited_bulkLog_of_scalar b s k X tb td G x h hs (rootExpr h)
    (compensationExpr h) hx.leaves hne
  have he := remaining_log_error h (l+1) _ hm center x
    (fun i hi => hx.source (.inr (.inl i)) (h.root.small.get i) rfl hi)
  have hC : sourceSum (fixedCenter center) (Template.remainder (l+1)
      (Template.current (Template.initial (2*b) k) l)) = (2:ℝ)^l*inheritedCenter b k l center :=
    sourceSum_current_filter (fixedCenter center) _ _ l
  have hN := fixedCount_current_filter_le
    (fun q => decide (q.role ≠ .compensation (l+1))) (2*b) k l
  change sourceSum fixedCount (Template.remainder (l+1)
    (Template.current (Template.initial (2*b) k) l)) ≤ (2:ℝ)^l*(6+4*(k:ℝ)) at hN
  rw [hC] at he
  have hp : (((diagonalRoleKeys h (fun q => decide (q.role ≠ .compensation (l+1)))).map x).prod) ≠ 0 :=
    (List.prod_pos (by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact hx.positive i)).ne'
  simp only [diagonalHKeys,List.map_cons,List.prod_cons]
  rw [Real.log_mul (hx.positive (.inl true)).ne' hp,log_role_product h _ x hx.positive]
  simp only [decide_eq_true_eq]
  have hg := hx.giant true
  have ha := (abs_add_le (Real.log (x (.inl true))-G)
    (bulkLog h.root.small (rootExpr h).small x-(2:ℝ)^l*(2*tb))).trans (add_le_add hg hb)
  have hh := (abs_add_le _ _).trans (add_le_add ha he)
  convert hh.trans (add_le_add_right hN (1+(2:ℝ)^l*2)) using 1
  · congr 1; ring
  · unfold inheritedWidth; ring

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
