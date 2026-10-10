import OAI.MeasureTheory.Falconer.Recursion.ScalarBunchingLedger

namespace OAI

/-! Total length, discarded weight and retained weight of the actual greedy
 bunching ledger. The loss and gain use the same covered terminal interval. -/
namespace Falconer

 theorem ScalarBunchChain.weight_partition {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) (w : ℕ → ℝ) :
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum +
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum =
        ∑ i ∈ Finset.Ico lo N, w i := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hp := Finset.sum_Ico_consecutive w h.start_le
      (b.start_lt_cut.le.trans b.cut_le_stop)
    have hb := Finset.sum_Ico_consecutive w b.start_lt_cut.le b.cut_le_stop
    simp only [List.map_cons,List.sum_cons]
    linarith

 theorem ScalarBunchChain.total_trim {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) {w : ℕ → ℝ} {theta : ℝ}
    (hg : ∀ b ∈ bs, ScalarBunchGood w theta b) :
    100*(bs.map (fun b => b.stop-b.cut)).sum ≤ N-lo := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hb := (hg b (by simp)).trim_budget
    have hi := ih (fun c hc => hg c (by simp [hc]))
    have ho := h.start_le
    have hc := b.cut_le_stop
    have ha := b.start_lt_cut
    simp only [List.map_cons,List.sum_cons]
    omega

 theorem ScalarBunchChain.total_loss {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) {w : ℕ → ℝ} {theta : ℝ}
    (hg : ∀ b ∈ bs, ScalarBunchGood w theta b) :
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum ≤
      theta*((N-lo:ℕ):ℝ)/100 := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hb := (hg b (by simp)).loss
    have hi := ih (fun c hc => hg c (by simp [hc]))
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have ho := h.start_le
      have hc := b.cut_le_stop
      have ha := b.start_lt_cut
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [he]
    linarith

 theorem ScalarBunchChain.total_retained {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) {w : ℕ → ℝ} {theta : ℝ}
    (hg : ∀ b ∈ bs, ScalarBunchGood w theta b) :
    (99/100:ℝ)*theta*((N-lo:ℕ):ℝ) ≤
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hb := (hg b (by simp)).retained
    have hi := ih (fun c hc => hg c (by simp [hc]))
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have ho := h.start_le
      have hc := b.cut_le_stop
      have ha := b.start_lt_cut
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [he]
    linarith

 theorem scalar_bunching_total_weights (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) (N : ℕ) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain N lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood w theta b) ∧
      (∑ i ∈ Finset.range lo, w i) ≤ theta*(lo:ℝ) ∧
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum ≤ theta*((N-lo:ℕ):ℝ)/100 ∧
      (99/100:ℝ)*theta*((N-lo:ℕ):ℝ) ≤
        (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum := by
  obtain ⟨lo,bs,h,hg,hs⟩ := scalar_bunching_ledger w htheta N
  refine ⟨lo,bs,h,hg,?_,h.total_loss hg,h.total_retained hg⟩
  simpa only [Nat.sub_self,Nat.Ico_zero_eq_range] using hs lo le_rfl

end Falconer

end OAI
