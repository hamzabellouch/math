import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.PublicCapLaw

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical

lemma capture_log_ratio (a c w z T : ℝ) (ha : 0<a) (hc : 0<c)
    (hw : 0<w) (hz : 0<z) (hcap : c*a≤z) (hsize : w≤a*Real.exp T) :
    Real.log (w/z)≤T-Real.log c := by
  have hlw := Real.log_le_log hw hsize
  have hlz := Real.log_le_log (mul_pos hc ha) hcap
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne',Real.log_exp] at hlw
  rw [Real.log_mul hc.ne' ha.ne'] at hlz
  rw [Real.log_div hw.ne' hz.ne']
  linarith

lemma reciprocal_capture_log_ratio (a b Q c k loss y z : ℝ)
    (ha : 0<a) (hb : 0<b) (hQ : 0<Q) (hc : 0<c) (hk : 0<k)
    (hy : 0<y) (hz : 0<z) (hprod : Q*Real.exp (-loss)≤a*b)
    (hsize : y≤k*Q/a) (hcap : c*b≤z) :
    Real.log (y/z)≤loss+Real.log k-Real.log c := by
  have hly := Real.log_le_log hy hsize
  have hlz := Real.log_le_log (mul_pos hc hb) hcap
  have hp := Real.log_le_log (mul_pos hQ (Real.exp_pos _)) hprod
  rw [Real.log_div (mul_pos hk hQ).ne' ha.ne',Real.log_mul hk.ne' hQ.ne'] at hly
  rw [Real.log_mul hc.ne' hb.ne'] at hlz
  rw [Real.log_mul hQ.ne' (Real.exp_pos _).ne',Real.log_exp,
    Real.log_mul ha.ne' hb.ne'] at hp
  rw [Real.log_div hy.ne' hz.ne']
  linarith

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem two_public_cap_cost (S W : Finset A) (T U Y : Finset B)
    (hS : S.Nonempty) (hW : W.Nonempty) (hT : T.Nonempty)
    (q c b P : ℝ) (d nA nB : ℕ) (hq : 1≤q) (hc : 0<c)
    (hcap : c*S.card≤(S∩W).card) (hWsize : (W.card:ℝ)≤S.card*Real.exp P)
    (hprod : q^(d+1)*Real.exp (-b)≤(S.card:ℝ)*T.card)
    (hY : ValidCap T U ((320/c+320)*q^(d+1)/S.card) Y) :
    Real.log (uniformCutoff q (S∩W) W nB)+Real.log (uniformCutoff q (T∩Y) Y nA)≤
      2*(Real.log (2*q)-Real.log ((9:ℝ)/10))+
      (nB:ℝ)*(P-Real.log c)+(nA:ℝ)*(b+Real.log (320/c+320)-Real.log ((9:ℝ)/10)) := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have ht : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have hcw : (0:ℝ)<(S∩W).card := lt_of_lt_of_le (mul_pos hc hs) hcap
  have hSW : (S∩W).Nonempty := Finset.card_pos.mp (by exact_mod_cast hcw)
  have hTY := hY.source_nonempty hT
  have hYn : Y.Nonempty := hTY.mono Finset.inter_subset_right
  have hposq : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hlB := uniformCutoff_log q hq (S∩W) W hSW hW Finset.inter_subset_right nB
  have hlA := uniformCutoff_log q hq (T∩Y) Y hTY hYn Finset.inter_subset_right nA
  have hrB := capture_log_ratio (S.card:ℝ) c W.card (S∩W).card P hs hc
    (by exact_mod_cast hW.card_pos) hcw hcap hWsize
  have hrA := reciprocal_capture_log_ratio (S.card:ℝ) T.card (q^(d+1)) ((9:ℝ)/10)
    (320/c+320) b Y.card (T∩Y).card hs ht (pow_pos hposq _) (by norm_num)
    (by positivity) (by exact_mod_cast hYn.card_pos) (by exact_mod_cast hTY.card_pos)
    hprod hY.2.1 hY.2.2
  have hmB := mul_le_mul_of_nonneg_left hrB (show (0:ℝ)≤nB by positivity)
  have hmA := mul_le_mul_of_nonneg_left hrA (show (0:ℝ)≤nA by positivity)
  linarith

end SharpRamseyFive.ReverseCap

end OAI
