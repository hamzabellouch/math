import OAI.NumberTheory.Jacobsthal.Estimates.CandidateLengthBand

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.MovingStopBandParameters
open _root_.Filter FinitePathGeometry PrimeHistories SourceStopPredicate SourceStopWindow
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open MarkedPrefixTools MarkedSourceSmallness ErdosPrimeInputs.HarmonicPrimeMeasure

theorem moving_stop_band_conditions (Clen xi : ℝ) (hxi : 0 ≤ xi) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ 1 ≤ Real.log w ∧ 401 ≤ K*(Real.log w)^2 ∧
      2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2) ∧
      xi/Real.log w ≤ (K*(Real.log w)^2)/2 := by
  let M := max 401 (max (2*xi) (50*(2*Clen*xi+(218/100)*xi)+1))
  filter_upwards [moving_compact_gap_small (6*M) hK,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hm hlog hw
  have hb : M < K*(Real.log w)^2 := by linarith
  have h₁ : (401:ℝ) ≤ M := le_max_left _ _
  have h₂ : 2*xi ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 50*(2*Clen*xi+(218/100)*xi)+1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hd := div_le_self hxi hlog
  exact ⟨hw,hlog,by linarith,by linarith,by linarith⟩

theorem last_prime_cutoff_power {w : ℝ} (hw : 1 < w) (z : Node) (ps : List ℕ)
    (hne : ps ≠ []) (hP : 0 < (ps.getLastD 0:ℝ)) :
    w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hw),terminal_lastD w z ps hne,primeExponent]
  have he : Real.log w*(Real.log (ps.getLastD 0:ℝ)/Real.log w)=Real.log (ps.getLastD 0:ℝ) := by
    field_simp [(Real.log_pos hw).ne']
  rw [he,Real.exp_log hP]

theorem candidate_moving_last_prime_lower (Y : ℕ) {w top Cs eta Clen B xi K b₁ : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hcomp : Real.log B ≤ 2*Real.log w)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*(K*(Real.log w)^2))
    (hhalf : xi/Real.log w ≤ (K*(Real.log w)^2)/2)
    (residue : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi (K*(Real.log w)^2) b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps) :
    Real.exp ((K/2)*(Real.log w)^3) ≤ (ps.getLastD 0:ℝ) ∧
      w^(terminal w z ps).cutoff=(ps.getLastD 0:ℝ) := by
  have hwindow := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hsource := candidate_source_primes Y hw htop hxi residue z ps hc
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hP : 0 < (ps.getLastD 0:ℝ) := by exact_mod_cast hprime.1.pos
  refine ⟨?_,last_prime_cutoff_power hw z ps hc.1 hP⟩
  have hcut : (K*(Real.log w)^2)/2 ≤ (terminal w z ps).cutoff := by linarith [hwindow.1]
  have hlogP : Real.log (ps.getLastD 0:ℝ)=(terminal w z ps).cutoff*Real.log w := by
    rw [terminal_lastD w z ps hc.1,primeExponent,div_mul_cancel₀ _ (Real.log_pos hw).ne']
  rw [← Real.exp_log hP]
  apply Real.exp_le_exp.mpr
  calc
    _ = ((K*(Real.log w)^2)/2)*Real.log w := by ring
    _ ≤ (terminal w z ps).cutoff*Real.log w := mul_le_mul_of_nonneg_right hcut (Real.log_pos hw).le
    _ = _ := hlogP.symm
end NumberTheoryLean.MovingStopBandParameters


end Erdos970

end OAI
