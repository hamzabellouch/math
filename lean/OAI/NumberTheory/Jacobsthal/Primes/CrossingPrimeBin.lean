import OAI.NumberTheory.Jacobsthal.Paths.RepeatedWordData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CrossingPrimeBin
open FinitePathGeometry PrimeHistories PrimeTiltGeometry RepeatedWordData CandidateTerminalGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open IsolatedBinGeometry MarkedPrefixTools
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def isolatedAlpha (theta T : ℝ) : ℝ := theta/(10*(T+1))

theorem isolated_alpha_bounds {theta T : ℝ} (htheta : 0 < theta) (hT : 1 ≤ T) :
    0 < isolatedAlpha theta T ∧ isolatedAlpha theta T ≤ theta := by
  unfold isolatedAlpha
  refine ⟨div_pos htheta (by linarith),?_⟩
  exact div_le_self htheta.le (by linarith)

theorem crossing_exponent_room {theta T B r s x h : ℝ} (htheta : 0 < theta) (hT : 1 ≤ T)
    (hB : 0 < B) (hx : 0 < x) (hs : (1:ℝ)/2 ≤ s) (hsT : s ≤ T)
    (he : r=s*x) (hlo : theta*B/3 < r) (hhi : r ≤ theta*B)
    (hh : h ≤ isolatedAlpha theta T*B) :
    isolatedAlpha theta T*B+h ≤ x ∧ x+h ≤ (4*theta)*B := by
  have ha := isolated_alpha_bounds htheta hT
  have hA : 0 ≤ isolatedAlpha theta T*B := mul_nonneg ha.1.le hB.le
  have hEq : 10*(isolatedAlpha theta T*B)*(T+1)=theta*B := by
    unfold isolatedAlpha
    field_simp [show T+1 ≠ 0 by linarith]
  have hlo' : 2*(isolatedAlpha theta T*B) ≤ x := by
    by_contra! hn
    have hm := mul_lt_mul_of_pos_right hn (by linarith : 0 < T)
    have hr : r ≤ x*T := by rw [he]; nlinarith
    nlinarith
  have hhi' : x ≤ 2*(theta*B) := by rw [he] at hhi; nlinarith
  have hAB : isolatedAlpha theta T*B ≤ theta*B := mul_le_mul_of_nonneg_right ha.2 hB.le
  exact ⟨by linarith,by nlinarith⟩

theorem actual_crossing_bin {w top xi ell S theta T B : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hell : 1 ≤ ell)
    (htheta : 0 < theta) (hT : 1 ≤ T) (hB : 0 < B) (z : Node)
    (hs : Valid z.side z.ratio) (hcap : w^z.cutoff=top)
    (h : History w ell S z) (hne : h.primes ≠ [])
    (hlo : theta*B/3 < h.node.gap) (hhi : h.node.gap ≤ theta*B) (hbound : h.node.ratio ≤ T)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta T*B) :
    isolatedBin w top xi B (isolatedAlpha theta T) (4*theta)
      (label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)) := by
  have hx := history_nonempty_cutoff_gt hw h hne
  have hx0 : 0 < h.node.cutoff := by linarith
  have hvalid : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hslo : (1:ℝ)/2 ≤ h.node.ratio := by
    cases he : h.node.side <;> rw [he] at hvalid <;> dsimp [Valid] at hvalid <;> linarith
  have hratio := terminal_ratio_div_cutoff w z h.primes hne hx0.ne'
  change h.node.ratio=h.node.gap/h.node.cutoff at hratio
  have hgap : h.node.gap=h.node.ratio*h.node.cutoff := ((eq_div_iff hx0.ne').mp hratio).symm
  have hroom := crossing_exponent_room htheta hT hB hx0 hslo hbound hgap hlo hhi hwidth
  have hl : h.primes.getLastD 0 ∈ h.primes := history_last_mem h hne
  have hsrc := ActualRepeatedBinStep.history_source_primes hw htop hell hcap h _ hl
  have hcut : h.node.cutoff=primeExponent w (h.primes.getLastD 0) := terminal_lastD w z h.primes hne
  apply whole_bin_of_exponent_band hw htop hxi hsrc
  · rw [← hcut]; exact hroom.1
  · rw [← hcut]; exact hroom.2
end NumberTheoryLean.CrossingPrimeBin


end Erdos970

end OAI
