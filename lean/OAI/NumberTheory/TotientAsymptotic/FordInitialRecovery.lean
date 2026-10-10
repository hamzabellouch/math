import OAI.NumberTheory.TotientAsymptotic.FordInitialFactor

namespace OAI

/-! A first-cutoff state and its common rough factor recover the original tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_full_factor_state {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) (j : Fin b) :
    (fordFactorState t (Y 0)).left j=t.left j-1 ∧
      (fordFactorState t (Y 0)).right j=t.right j-1 := by
  have hY := ford_cutoff_antitone hp (Nat.zero_le j.val) j.isLt.le
  obtain ⟨_,_,_,_,hl,_,hr,_,_⟩ := h.2.1 j
  exact ⟨partBelow_all_of_largest_le (ford_shift_pos h j).1.ne' (hl.trans hY),
    partBelow_all_of_largest_le (ford_shift_pos h j).2.ne' (hr.trans hY)⟩

lemma ford_full_state_injective {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t s : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (ht : FordComparisonConditions b y S D r Y U t)
    (hs : FordComparisonConditions b y S D r Y U s)
    (he : fordFactorState t (Y 0)=fordFactorState s (Y 0)) : t=s := by
  have hl : t.left=s.left := by
    funext j
    have hh := congrArg (fun q : ShiftedPair b => q.left j) he
    rw [(ford_full_factor_state hp ht j).1,(ford_full_factor_state hp hs j).1] at hh
    have hp₁ := (ht.2.1 j).1.1.two_le
    have hp₂ := (hs.2.1 j).1.1.two_le
    omega
  have hr : t.right=s.right := by
    funext j
    have hh := congrArg (fun q : ShiftedPair b => q.right j) he
    rw [(ford_full_factor_state hp ht j).2,(ford_full_factor_state hp hs j).2] at hh
    have hp₁ := (ht.2.1 j).2.1.1.two_le
    have hp₂ := (hs.2.1 j).2.1.1.two_le
    omega
  have he₀ := congrArg (fun q : ShiftedPair b => q.remainder) he
  have he' : t.remainder=s.remainder := he₀
  cases t
  cases s
  cases hl
  cases hr
  cases he'
  rfl

lemma ford_initial_pair {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    fordBand hp.1 t Y=(fun _ => fordInitialFactor hp.1 t Y,fun _ => fordInitialFactor hp.1 t Y) := by
  have hl : (fordBand hp.1 t Y).1 0=fordInitialFactor hp.1 t Y := by
    simpa only [pairedProduct,Fin.prod_univ_one] using ford_initial_band hp h
  have hr : (fordBand hp.1 t Y).2 0=fordInitialFactor hp.1 t Y := by
    simpa only [pairedProduct,Fin.prod_univ_one,hl] using (ford_band_product_eq hp.1 hp h).symm
  apply Prod.ext
  · funext j; fin_cases j; exact hl
  · funext j; fin_cases j; exact hr

lemma ford_initial_recover {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t s : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (ht : FordComparisonConditions b y S D r Y U t)
    (hs : FordComparisonConditions b y S D r Y U s)
    (hlow : fordFactorState t (Y 1)=fordFactorState s (Y 1))
    (hn : fordInitialFactor hp.1 t Y=fordInitialFactor hp.1 s Y) : t=s := by
  have hUV := ford_cutoff_antitone hp (by omega : 0 ≤ 1) hp.1
  have hband : stateBand hp.1 (fordFactorState t (Y 0)) (Y 1) (Y 0)=
      stateBand hp.1 (fordFactorState s (Y 0)) (Y 1) (Y 0) := by
    rw [stateBand_fordFactorState hp.1 t le_rfl,stateBand_fordFactorState hp.1 s le_rfl]
    change fordBand hp.1 t Y=fordBand hp.1 s Y
    rw [ford_initial_pair hp ht,ford_initial_pair hp hs,hn]
  have htail (q : ShiftedPair b) (hq : FordComparisonConditions b y S D r Y U q) :
      ∀ j : Fin b,1 ≤ j.val →
      partBetween ((fordFactorState q (Y 0)).left j) (Y 1) (Y 0)=1 ∧
      partBetween ((fordFactorState q (Y 0)).right j) (Y 1) (Y 0)=1 := by
    intro j hj
    have hh := ford_band_tail hp hq j hj
    exact ⟨(partBetween_below _ le_rfl).trans hh.1,(partBetween_below _ le_rfl).trans hh.2⟩
  apply ford_full_state_injective hp ht hs
  apply lowerState_recover hp.1 hUV
    (fun j => ⟨partBelow_nested _ le_rfl,partBelow_nested _ le_rfl⟩)
    (fun j => ⟨partBelow_nested _ le_rfl,partBelow_nested _ le_rfl⟩)
    (htail t ht) (htail s hs) _ hband
  simpa only [lower_fordFactorState _ hUV] using hlow

end TotientAsymptotic

end

end OAI
