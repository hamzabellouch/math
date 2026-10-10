import Mathlib
import OAI.Combinatorics.KMedian.Optimization.OptimizationBitBound
import OAI.Combinatorics.KMedian.Compression.RationalOperationHeight

namespace OAI


                                                   
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient Binary
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem trajectory_height (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0<r) (hk : 0<k) (hH : 0<H)
    (R : ℤ) (hR : 0<R) (hd : ∀ j i, RationalGrid.At R (d j i))
    (L : ℕ) (hbase : rateDen (n:=n) (m:=m) r H*R*(n:ℤ) ≤ 2^L)
    (hkL : (k:ℤ) ≤ 2^L) (t : ℕ) (i : Fin n) :
    HasHeight (point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i) (L*(t+1)) := by
  let b := rateDen (n:=n) (m:=m) r H
  have hb : 0<b := rateDen_pos r H hr hH
  obtain ⟨Q,hQ,hBQ,hv⟩ := trajectory_denominator (n:=n) (k:ℤ) b R hb hR
    (fun y => gradient d y H) (fun y j => by
      exact_mod_cast gradient_grid d y R (H:ℤ) hR.ne' hd j) t
  let q := point (trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
      (fun y => gradient d y H) (initial (k:ℚ)) t) i
  have hqgrid : RationalGrid.At Q q := by
    dsimp only [q]
    rw [rate_eq]
    exact hv i
  have hkq : (0:ℚ)<k := by exact_mod_cast hk
  have hf := trajectory_feasible (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ)) hkq (initial_feasible _ hkq.le) t
  have hq0 : 0≤q := hf.1 i
  have hqk : q≤(k:ℚ) := (single_le_sum (fun j _ => hf.1 j) (mem_univ i)).trans_eq hf.2
  obtain ⟨A,hA⟩ := hqgrid
  change q=(A:ℚ)/(Q:ℚ) at hA
  have hQq : (0:ℚ)<Q := by exact_mod_cast hQ
  have hA0 : (0:ℤ)≤A := by
    have hh : (0:ℚ)≤A := by
      have hmul := mul_nonneg (hA ▸ hq0) hQq.le
      rwa [div_mul_cancel₀ _ hQq.ne'] at hmul
    exact_mod_cast hh
  have hAk : A≤(k:ℤ)*Q := by
    have hh := (div_le_iff₀ hQq).mp (hA ▸ hqk)
    exact_mod_cast hh
  have hQP : Q≤(2:ℤ)^(L*t) := by
    apply hBQ.trans
    rw [pow_mul]
    apply pow_le_pow_left₀ (le_of_lt (mul_pos (mul_pos hb hR) (by exact_mod_cast NeZero.pos n))) hbase
  have hAP : |A|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_nonneg hA0]
    calc
      _ ≤ (k:ℤ)*Q := hAk
      _ ≤ (2:ℤ)^L*(2:ℤ)^(L*t) := mul_le_mul hkL hQP hQ.le (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hQP' : |Q|≤(2:ℤ)^(L*(t+1)) := by
    rw [abs_of_pos hQ]
    exact hQP.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (Nat.le_succ _)))
  change HasHeight q _
  rw [hA]
  exact Gaussian.ratio_num_den_bound A Q hQ.ne' _ hAP hQP'
end MetricKMedian.TruncatedLP
end

end OAI
