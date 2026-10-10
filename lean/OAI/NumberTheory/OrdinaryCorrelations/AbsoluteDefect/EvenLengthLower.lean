import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinQ

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open Finset OrdinaryNarrowGrid

attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

lemma even_length_lower (X : ℕ) {i : ℕ×ℕ} (hi : 0<upper i) (hX : 2*upper i≤X) :
    X≤2*upper i*evenBinLength X i := by
  have hq : 1≤X/(2*upper i) := Nat.div_pos hX (by omega)
  have hh := Nat.lt_mul_div_succ X (by omega : 0<2*upper i)
  unfold evenBinLength
  nlinarith

lemma amplifier_height {B H s j X : ℕ} (hB : H+10≤B)
    (hX : 2*2^(F B s (j+1))≤X) {a i : ℕ×ℕ}
    (ha : a∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (hi : i∈grid (binQ B H s (j+1)) (binStart B H s (j+1)) (binWidth B s (j+1))) :
    2*X≤(2*lower a)^(amplifier (binLog B H s j a) (binLog B H s (j+1) i))*evenBinLength X i := by
  let L := binLog B H s j a
  let M := binLog B H s (j+1) i
  let k := amplifier L M
  have hL : 0<L := (E_pos B s j).trans_le (bin_log_range (B:=B) (H:=H) (s:=s) (j:=j) hB ha).1
  have hpow : 4*upper i≤(2*lower a)^k := by
    have hup := (bin_lower_bounds (B:=B) (H:=H) (s:=s) (j:=j+1) hi).2
    have hlo := (bin_lower_bounds (B:=B) (H:=H) (s:=s) (j:=j) ha).1
    change 2^L≤lower a at hlo
    have hk := amplifier_lower (M:=M) hL
    calc
      4*upper i ≤ 4*2^(M+1) := Nat.mul_le_mul_left _ hup
      _ = 2^(M+3) := by rw [show M+3=(M+1)+2 by omega,pow_add]; ring
      _ ≤ 2^(L*k) := Nat.pow_le_pow_right (by omega) hk.le
      _ = (2^L)^k := pow_mul _ _ _
      _ ≤ (2*lower a)^k := Nat.pow_le_pow_left (by omega) _
  have hu : 0<upper i :=
    (grid_lower_pos _ _ _ (by unfold binQ; positivity) hi).trans_le (lower_le_upper i)
  have hiU := upper_le_endpoint _ _ _ hi
  rw [(window_endpoints B H s (j+1) hB).2] at hiU
  have hX' : 2*upper i≤X := (Nat.mul_le_mul_left _ hiU).trans hX
  have hh := even_length_lower X hu hX'
  have hm := Nat.mul_le_mul_right (evenBinLength X i) hpow
  change 2*X≤(2*lower a)^k*evenBinLength X i
  nlinarith

end OrdinaryChainScales

end

end OAI
