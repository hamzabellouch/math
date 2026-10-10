import OAI.NumberTheory.TwoPoint.Circuits.CircuitOrCertificate

namespace OAI

/-! The recursive error certificate has polynomial size. Only this coarse
bound, rather than the detailed shape of its gates, is used by the next stage. -/

namespace TwoPointCorrelations.AC0Circuit

open Finset
open scoped Classical

def exceptionPolynomialBound (m s : ℕ) : ℕ :=
  5 + m + s * (Nat.log 2 m + 3) * (1 + m * (1 + m))

theorem exceptionSizeBound_le {n : ℕ} (s : ℕ) (c : AC0Circuit n)
    (m : ℕ) (hm : c.size ≤ m) :
    c.exceptionSizeBound s ≤ exceptionPolynomialBound m s * c.size := by
  induction c generalizing m with
  | literal i b =>
    simp only [exceptionSizeBound, size, mul_one, exceptionPolynomialBound]
    omega
  | @andGate k c ih | @orGate k c ih =>
    have hm' : 1 + ∑ i, (c i).size ≤ m := hm
    have hsize (i : Fin k) : (c i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (c j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (c i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (c i).size_pos)
    have hk : k ≤ m := by omega
    have hsum : ∑ i, (c i).exceptionSizeBound s ≤
        exceptionPolynomialBound m s * ∑ i, (c i).size := by
      rw [mul_sum]
      exact sum_le_sum (fun i _ => ih i m (hsize i))
    have hlocal : 4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) ≤ exceptionPolynomialBound m s := by
      unfold exceptionPolynomialBound
      have hsumsize : ∑ i, (c i).size ≤ m := by omega
      have hlog := Nat.log_mono_right (b := 2) hk
      gcongr
      norm_num
    change 4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s ≤
      exceptionPolynomialBound m s * (1 + ∑ i, (c i).size)
    calc
      _ ≤ exceptionPolynomialBound m s +
          exceptionPolynomialBound m s * ∑ i, (c i).size := Nat.add_le_add hlocal hsum
      _ = _ := by ring

end TwoPointCorrelations.AC0Circuit

end OAI
