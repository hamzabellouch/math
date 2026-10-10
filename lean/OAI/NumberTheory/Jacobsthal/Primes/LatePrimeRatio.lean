import OAI.NumberTheory.Jacobsthal.Paths.RepeatedWordData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LatePrimeRatio
open FinitePathGeometry PrimeHistories PrimeTiltGeometry RepeatedWordData

attribute [local instance] Classical.propDecidable

theorem child_ratio_min {w ell S : ℝ} (z : Node) {p : ℕ} (hp : p ∈ nodeChildren w ell S z) :
    minRatio z.side z.ratio ≤ (step w z p).ratio := (Finset.mem_filter.mp hp).2.2.2.1

theorem two_step_ratio_one {w ell S : ℝ} (z : Node) {p q : ℕ}
    (hp : p ∈ nodeChildren w ell S z) (hq : q ∈ nodeChildren w ell S (step w z p)) :
    1 ≤ (step w (step w z p) q).ratio := by
  have h1 := child_ratio_min z hp
  have h2 := child_ratio_min (step w z p) hq
  cases hi : z.side with
  | even =>
    have hside : (step w z p).side=.odd := by simp [step,hi,Side.flip]
    rw [hside] at h2
    exact (by norm_num : (1:ℝ)≤2).trans ((le_max_left _ _).trans h2)
  | odd =>
    rw [hi] at h1
    have hfirst : 2 ≤ (step w z p).ratio := (le_max_left _ _).trans h1
    have hside : (step w z p).side=.even := by simp [step,hi,Side.flip]
    rw [hside] at h2
    change (step w z p).ratio-1 ≤ (step w (step w z p) q).ratio at h2
    linarith

theorem allowed_late_ratio_one {w ell S : ℝ} (z : Node) (ps : List ℕ)
    (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) : 1 ≤ (terminal w z ps).ratio := by
  induction ps generalizing z with
  | nil => simp at hlen
  | cons p ps ih =>
    obtain ⟨hhead,hrest⟩ := (allowed_cons w ell S z p ps).mp hp
    cases ps with
    | nil => simp at hlen
    | cons q qs =>
      cases qs with
      | nil =>
        have hq := ((allowed_cons w ell S (step w z p) q []).mp hrest).1
        exact two_step_ratio_one z hhead hq
      | cons r rs => exact ih (step w z p) hrest (by simp)

theorem allowed_late_gap_cutoff {w ell S : ℝ} (hw : 1 < w) (hell : 1 ≤ ell)
    (z : Node) (ps : List ℕ) (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) :
    (terminal w z ps).cutoff ≤ (terminal w z ps).gap := by
  have hne : ps ≠ [] := by intro he; simp [he] at hlen
  let h : History w ell S z := ⟨ps,hp⟩
  have hx := history_nonempty_cutoff_gt hw h hne
  have hx0 : 0 < (terminal w z ps).cutoff := by change ell < (terminal w z ps).cutoff at hx; linarith
  have hr := allowed_late_ratio_one z ps hp hlen
  have he := CandidateTerminalGeometry.terminal_ratio_div_cutoff w z ps hne hx0.ne'
  rw [he] at hr
  exact (one_le_div hx0).mp hr
end NumberTheoryLean.LatePrimeRatio


end Erdos970

end OAI
