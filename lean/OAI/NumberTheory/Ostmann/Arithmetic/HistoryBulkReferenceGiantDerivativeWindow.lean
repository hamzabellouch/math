import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeWindow
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern
open HistoryBulkCorrectedXiBounds

theorem actual_history_H_window_relaxed (b s k l : ℕ) (X tb td G : ℝ) (center : ℕ → ℝ)
    {V : ℕ → ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hm : Template.Matches (Template.current (Template.initial (2*b) k) l) h.root.small)
    (x : Key h → ℝ) (hx : ∀i, 0 < x i)
    (hsource : IndependentSourceCells (independentSlot h) center x)
    (hleaves : ∀a∈h.leafStates, Template.Matches (Template.initial (2*b) k) a.small)
    (hg : |Real.log (x (.inl true))-G| ≤ 2)
    (hne : actualRealHistoryScalar b s X tb td G outside h hs x ≠ 0) :
    |Real.log (((diagonalHKeys h (l+1)).map x).prod) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l+1 := by
  have hb := inherited_bulkLog_of_scalar b s k X tb td G x h hs (rootExpr h)
    (compensationExpr h) hleaves hne
  have he := remaining_log_error h (l+1) _ hm center x
    (fun i hi => hsource (.inr (.inl i)) (h.root.small.get i) rfl hi)
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
      exact hx i)).ne'
  simp only [diagonalHKeys,List.map_cons,List.prod_cons]
  rw [Real.log_mul (hx (.inl true)).ne' hp,log_role_product h _ x hx]
  simp only [decide_eq_true_eq]
  have ha := (abs_add_le (Real.log (x (.inl true))-G)
    (bulkLog h.root.small (rootExpr h).small x-(2:ℝ)^l*(2*tb))).trans (add_le_add hg hb)
  have hh := (abs_add_le _ _).trans (add_le_add ha he)
  convert hh.trans (add_le_add_right hN (2+(2:ℝ)^l*2)) using 1
  · congr 1; ring
  · unfold inheritedWidth; ring

theorem inherited_window_normalize_add_one (b k l : ℕ) (logH G tb J Δ : ℝ)
    (w center : ℕ → ℝ)
    (hH : |logH-(G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l+1)
    (ht : |(∑h,∑i,InitialCoordinatesTemplate.topCenters b center h i)-(J-2*tb)| ≤ 2)
    (hc : ∀j<k,|typeCenter b j center-w j| ≤ 2)
    (hw : (2:ℝ)^l*(J+∑j∈Finset.Ico (l+1) k,w j) = (2:ℝ)^l*w l+Δ) :
    |logH-(G+(2:ℝ)^l*w l+Δ)| ≤ nominalInheritedWidth k l+1 := by
  have hC := inheritedCenter_nominal_error b k l tb J w center ht hc
  have hr : 0 ≤ (2:ℝ)^l := by positivity
  have he := mul_le_mul_of_nonneg_left hC hr
  rw [←abs_of_nonneg hr,←abs_mul] at he
  rw [abs_of_nonneg hr] at he
  have hid : logH-(G+(2:ℝ)^l*w l+Δ) =
      (logH-(G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))) +
        (2:ℝ)^l*(2*tb+inheritedCenter b k l center-(J+∑j∈Finset.Ico (l+1) k,w j)) := by
    rw [mul_sub,hw]
    ring
  rw [hid]
  have ha := (abs_add_le _ _).trans (add_le_add hH he)
  convert ha using 1
  unfold nominalInheritedWidth inheritedWidth
  ring

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem paired_H_window_relaxed (b s k₀ : ℕ) (X tb td G : ℝ) (center : ℕ → ℝ)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hk : TreeSourceLabels (Template.initial (2*b) k₀) k)
    (x : PairKey h k → ℝ) (hx : ∀i,0 < x i)
    (hsource : IndependentSourceCells (independentSlot k) center (fun i => x (rightMap h k i)))
    (hleaves : ∀a∈k.leafStates,Template.Matches (Template.initial (2*b) k₀) a.small)
    (hg : |Real.log (x (rightMap h k (.inl true)))-G| ≤ 2)
    (hne : pairedRealXi b s X tb td G h k hs ks x ≠ 0) :
    |Real.log (((pairedDiagonalHKeys h k (l+1)).map x).prod) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k₀ l center))| ≤ inheritedWidth k₀ l+1 := by
  have hn : actualRealHistoryScalar b s X tb td G outside k ks
      (fun i => x (rightMap h k i)) ≠ 0 := by
    intro hz
    exact hne (by simp only [pairedRealXi,actualRealXi,hz,star_zero,mul_zero])
  simpa only [pairedDiagonalHKeys,List.map_map,Function.comp_def] using
    actual_history_H_window_relaxed b s k₀ l X tb td G center k ks (root_matches hk)
      (fun i => x (rightMap h k i)) (fun i => hx _) hsource hleaves hg hn

theorem selected_paired_H_window_relaxed {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (s : ℕ) (hl : l < k₀) (X : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (x : PairKey h k → ℝ) (hx : ∀i,0 < x i)
    (hsource : IndependentSourceCells (independentSlot k) (C.cells.center (bulkSize k₀ L/2))
      (fun i => x (rightMap h k i)))
    (hleaves : ∀a∈k.leafStates,
      Template.Matches (Template.initial (2*(bulkSize k₀ L/2)) k₀) a.small)
    (hg : |Real.log (x (rightMap h k (.inl true)))-(C.giantCenter:ℝ)| ≤ 2)
    (hne : pairedRealXi (bulkSize k₀ L/2) s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks x ≠ 0) :
    |Real.log (((pairedDiagonalHKeys h k (l+1)).map x).prod) -
      ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l)| ≤
      nominalInheritedWidth k₀ l+1 := by
  apply inherited_window_normalize_add_one (bulkSize k₀ L/2) k₀ l _ C.giantCenter C.bulkBin
    (nominalJ Bs BD Bz k₀ L C.blockBase C.giantCenter C.spectatorBin)
    (stepGap BD Bz k₀ L l) (nominalWeight k₀
      (nominalJ Bs BD Bz k₀ L C.blockBase C.giantCenter C.spectatorBin) (stepGap BD Bz k₀ L))
    (C.cells.center (bulkSize k₀ L/2)) _ (C.top_frequency_center_error _)
    (C.type_frequency_center_error _) (nominalWeight_recurrence_scaled hl _ _)
  exact paired_H_window_relaxed _ s k₀ X C.bulkBin C.spectatorBin C.giantCenter _
    h k hs ks hk x hx hsource hleaves hg hne

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeWindow

end

end OAI
