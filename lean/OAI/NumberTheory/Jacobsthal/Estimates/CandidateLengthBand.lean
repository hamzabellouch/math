import OAI.NumberTheory.Jacobsthal.Paths.SourceStopWindow
import OAI.NumberTheory.Jacobsthal.Paths.StopLengthBandGeometry
import OAI.NumberTheory.Jacobsthal.Primes.PrimeProductLogCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateLengthBand
open FinitePathGeometry PrimeHistories SourceStopPredicate SourceStopWindow PrimeProductLogCoordinates
open StopLengthBandGeometry MarkedPrefixTools LogarithmicBinScale LogarithmicBinEndpoints
open LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem candidate_whole_bin_length_band (Y : ℕ) (hY : 0 < Y)
    {w top Cs eta Clen B xi b₀ b₁ alpha : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hC : 0 ≤ Clen) (hcomp : Real.log B ≤ 2*Real.log w) (hlogw : 1 ≤ Real.log w)
    (hb₀ : 401 ≤ b₀) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hsmall : 2*Clen*xi+(218/100)*(xi/Real.log w) ≤ (2/100)*b₀)
    (residue : ℕ → ℕ) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-alpha+2) (ps : List ℕ)
    (hc : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) residue z ps)
    (p₀ q : ℕ) (hq : 0 < q) (hprod : ps.prod=p₀*q)
    {R zeta : ℝ} (hR : 0 < R) (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hp₀ : R ≤ (p₀:ℝ) ∧ (p₀:ℝ) ≤ (1+zeta)*R)
    (p : ℝ) (hp : R ≤ p ∧ p ≤ (1+zeta)*R) :
    203/100 ≤ Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ∧
      Real.log ((Y:ℝ)/(p*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ) ≤ 219/100 := by
  have hwindow := candidate_actual_window Y hw htop hxi hC hcomp hsmall residue z ps hc
  have hsource := candidate_source_primes Y hw htop hxi residue z ps hc
  have hpos : ∀ p ∈ ps,0 < p := fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos
  have hlast : ps.getLastD 0 ∈ ps := by
    have he : ps.getLastD 0=ps.getLast hc.1 := by
      conv_lhs => rw [← List.dropLast_append_getLast hc.1]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hc.1
  have hprime := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop _).mp (hsource _ hlast)
  have hP : 1 < ps.getLastD 0 := hprime.1.one_lt
  have hstep : xi/Real.log w ≤ 1 := (div_le_self hxi.le hlogw).trans hxi1
  have hb : 400 ≤ (terminal w z ps).cutoff := by linarith [hwindow.1]
  have hlogP : 200 ≤ Real.log (ps.getLastD 0:ℝ) := by
    have he : Real.log (ps.getLastD 0:ℝ)=(terminal w z ps).cutoff*Real.log w := by
      rw [terminal_lastD w z ps hc.1,primeExponent,div_mul_cancel₀ _ (Real.log_pos hw).ne']
    rw [he]
    nlinarith
  have hid := source_length_exponent_identity hw Y (ps.getLastD 0) hY hP z hroot ps hpos
  rw [← terminal_lastD w z ps hc.1] at hid
  have hband : 2035/1000 ≤ Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) ∧
      Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) ≤ 218/100 := by
    rw [hid]
    exact shifted_ratio_band hb ha0 ha1 hwindow.2.2.1 hwindow.2.2.2
  have he₀ : Real.log ((Y:ℝ)/((p₀:ℝ)*(q:ℝ)))/Real.log (ps.getLastD 0:ℝ)=
      Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (ps.getLastD 0:ℝ) := by rw [hprod,Nat.cast_mul]
  exact whole_bin_length_band (by exact_mod_cast hY) (by exact_mod_cast hq) hR hzeta hzeta1 hp hp₀ hlogP he₀ hband
end NumberTheoryLean.CandidateLengthBand


end Erdos970

end OAI
