import OAI.MeasureTheory.Falconer.Estimates.ScalarBunchingSuffix

namespace OAI

/-! A finite greedy ledger for porous bunches. Its intervals partition
 a terminal range, and every omitted tail has a controlled weight loss. -/
namespace Falconer

structure ScalarBunch where
  start : ℕ
  cut : ℕ
  stop : ℕ
  start_lt_cut : start < cut
  cut_le_stop : cut ≤ stop

inductive ScalarBunchChain : ℕ → ℕ → List ScalarBunch → Prop
  | nil (n : ℕ) : ScalarBunchChain n n []
  | cons (b : ScalarBunch) {lo : ℕ} {bs : List ScalarBunch}
      (h : ScalarBunchChain b.start lo bs) : ScalarBunchChain b.stop lo (b :: bs)

structure ScalarBunchGood (w : ℕ → ℝ) (theta : ℝ) (b : ScalarBunch) : Prop where
  loss : (∑ i ∈ Finset.Ico b.cut b.stop, w i) ≤ theta*((b.stop-b.start:ℕ):ℝ)/100
  retained : (99/100:ℝ)*theta*((b.stop-b.start:ℕ):ℝ) ≤ ∑ i ∈ Finset.Ico b.start b.cut, w i
  trim_budget : 100*(b.stop-b.cut) ≤ b.stop-b.start
  gap : (b.stop = b.cut ∧ b.stop-b.start ≤ 1000) ∨ b.stop-b.start ≤ 200*(b.stop-b.cut)

 theorem scalar_minimal_heavy_suffix_of_exists (w : ℕ → ℝ) (theta : ℝ) (N : ℕ)
    (hex : ∃ r ≤ N, theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i) :
    ∃ r, 0 < r ∧ r ≤ N ∧ theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i ∧
      ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ) := by
  let P := fun r : ℕ => r ≤ N ∧ theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i
  have hex' : ∃ r, P r := hex
  let r := Nat.find hex'
  have hr := Nat.find_spec hex'
  have hr0 : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    have hx := hr.2
    change theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i at hx
    simp only [hz,Nat.sub_zero,Finset.Ico_self,Finset.sum_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hx
  refine ⟨r,hr0,hr.1,hr.2,?_⟩
  intro s hs
  have hh := Nat.find_min hex' hs
  exact le_of_not_gt (fun he => hh ⟨by omega,he⟩)

 theorem scalar_bunching_ledger (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) (N : ℕ) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain N lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood w theta b) ∧
      ∀ r ≤ lo, (∑ i ∈ Finset.Ico (lo-r) lo, w i) ≤ theta*(r:ℝ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hex : ∃ r ≤ N, theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i
    · obtain ⟨r,hr0,hrN,hr,hmin⟩ := scalar_minimal_heavy_suffix_of_exists w theta N hex
      let t := scalarBunchTrim r
      have ht : t < r := scalarBunchTrim_lt hr0
      let b : ScalarBunch := ⟨N-r,N-t,N,by omega,by omega⟩
      have hlen : b.stop-b.start = r := by dsimp [b]; omega
      have htail : b.stop-b.cut = t := by dsimp [b]; omega
      have hgood : ScalarBunchGood w theta b := by
        have hw := scalar_bunch_retained_weight w htheta N r hr0 hrN hr hmin
        refine ⟨?_,?_,?_,?_⟩
        · simpa only [b,hlen] using hw.1
        · exact (show (99/100:ℝ)*theta*((b.stop-b.start:ℕ):ℝ) <
            ∑ i ∈ Finset.Ico b.start b.cut, w i from by simpa only [b,hlen] using hw.2).le
        · rw [hlen,htail]
          exact scalarBunchTrim_budget r
        · by_cases hrs : r ≤ 1000
          · left
            constructor
            · have ht0 : t = 0 := by simp [t,scalarBunchTrim,hrs]
              dsimp [b]
              omega
            · rwa [hlen]
          · right
            rw [hlen,htail]
            exact scalarBunchTrim_lower (by omega)
      obtain ⟨lo,bs,hchain,hgoods,hstop⟩ := ih (N-r) (by omega)
      refine ⟨lo,b :: bs,ScalarBunchChain.cons b hchain,?_,hstop⟩
      intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · subst c
        exact hgood
      · exact hgoods c hc
    · refine ⟨N,[],ScalarBunchChain.nil N,by simp,?_⟩
      intro r hr
      exact le_of_not_gt (fun h => hex ⟨r,hr,h⟩)

 theorem ScalarBunchChain.start_le {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) : lo ≤ N := by
  induction h with
  | nil n => exact le_rfl
  | cons b h ih => exact ih.trans (b.start_lt_cut.le.trans b.cut_le_stop)

 theorem ScalarBunchChain.total_length {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) : (bs.map (fun b => b.stop-b.start)).sum = N-lo := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    have horder : lo ≤ b.start := h.start_le
    have hb := b.start_lt_cut
    have hc := b.cut_le_stop
    omega


end Falconer

end OAI
