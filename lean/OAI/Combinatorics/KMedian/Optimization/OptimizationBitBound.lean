import Mathlib
import OAI.Combinatorics.KMedian.Optimization.TruncatedOptimization
import OAI.Combinatorics.KMedian.Compression.CircuitBitBound
import OAI.Combinatorics.KMedian.Optimization.SubgradientDenominator

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def rateDen (r H : ℕ) : ℤ := 2*(r:ℤ)*(gradSize (n:=n) (m:=m) H:ℤ)

theorem rateDen_pos (r H : ℕ) (hr : 0 < r) (hH : 0 < H) :
    0 < rateDen (n:=n) (m:=m) r H := by
  unfold rateDen
  have hg := gradSize_pos (n:=n) (m:=m) H hH
  have hri : (0:ℤ) < r := by exact_mod_cast hr
  have hgi : (0:ℤ) < gradSize (n:=n) (m:=m) H := by exact_mod_cast hg
  positivity

omit [NeZero n] [NeZero m] in
theorem rate_eq (r H : ℕ) : rate (n:=n) (m:=m) r H=
    1/(rateDen (n:=n) (m:=m) r H:ℚ) := by
  simp only [rate,rateDen,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]

theorem optimize_denominator (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H)
    (R : ℤ) (hR : 0 < R) (hd : ∀ j i, RationalGrid.At R (d j i)) :
    ∃ Q : ℤ, 0 < Q ∧
      Q ≤ (rateDen (n:=n) (m:=m) r H*R*(n:ℤ))^(steps (n:=n) (m:=m) r k H) ∧
      ∀ i, RationalGrid.At Q (point (optimize d r k H hr hk hH) i) := by
  let T := steps (n:=n) (m:=m) r k H
  let : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let b := rateDen (n:=n) (m:=m) r H
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  have hb : 0 < b := rateDen_pos r H hr hH
  have hn : (0:ℤ) < n := by exact_mod_cast NeZero.pos n
  have hbase : 1 ≤ b*R*(n:ℤ) := by
    have hpos : 0 < b*R*(n:ℤ) := mul_pos (mul_pos hb hR) hn
    omega
  obtain ⟨Q,hQ,hbQ,hv⟩ := trajectory_denominator (n:=n) (k:ℤ) b R hb hR
    (fun y => gradient d y H) (fun y i => by
      exact_mod_cast gradient_grid d y R (H:ℤ) hR.ne' hd i) a.val
  refine ⟨Q,hQ,hbQ.trans (pow_le_pow_right₀ hbase a.isLt.le),?_⟩
  intro i
  change RationalGrid.At Q (point (v a.val) i)
  dsimp only [v]
  rw [rate_eq]
  exact hv i

theorem optimize_bit_bound (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) (hd0 : ∀ j i, 0 ≤ d j i)
    (R : ℤ) (hR : 0 < R) (hd : ∀ j i, RationalGrid.At R (d j i))
    (L : ℕ) (hbase : rateDen (n:=n) (m:=m) r H*R*(n:ℤ) ≤ 2^L)
    (hkL : (k:ℤ) ≤ 2^L) (i : Fin n) :
    let q := point (optimize d r k H hr hk hH) i
    |q.num| ≤ (2:ℤ)^(L*(steps (n:=n) (m:=m) r k H+1)) ∧
      (q.den:ℤ) ≤ (2:ℤ)^(L*(steps (n:=n) (m:=m) r k H+1)) := by
  obtain ⟨Q,hQ,hBQ,hv⟩ := optimize_denominator d r k H hr hk hH R hR hd
  let q := point (optimize d r k H hr hk hH) i
  have hf := (optimize_spec d r k H hr hk hH hd0 (point (initial (k:ℚ)))
    (initial_feasible _ (by positivity))).1
  have hq0 : 0 ≤ q := hf.1 i
  have hqk : q ≤ (k:ℚ) := by
    exact (single_le_sum (fun j _ => hf.1 j) (mem_univ i)).trans_eq hf.2
  obtain ⟨A,hA⟩ := hv i
  change q=(A:ℚ)/(Q:ℚ) at hA
  have hQq : (0:ℚ) < Q := by exact_mod_cast hQ
  have hA0 : (0:ℤ) ≤ A := by
    have hh : (0:ℚ) ≤ A := by
      have hmul := mul_nonneg (hA ▸ hq0) hQq.le
      rwa [div_mul_cancel₀ _ hQq.ne'] at hmul
    exact_mod_cast hh
  have hAk : A ≤ (k:ℤ)*Q := by
    have hh := (div_le_iff₀ hQq).mp (hA ▸ hqk)
    exact_mod_cast hh
  have hQP : Q ≤ (2:ℤ)^(L*steps (n:=n) (m:=m) r k H) := by
    apply hBQ.trans
    rw [pow_mul]
    apply pow_le_pow_left₀ (le_of_lt (mul_pos (mul_pos (rateDen_pos r H hr hH) hR) (by exact_mod_cast NeZero.pos n))) hbase
  have hAP : |A| ≤ (2:ℤ)^(L*(steps (n:=n) (m:=m) r k H+1)) := by
    rw [abs_of_nonneg hA0]
    calc
      _ ≤ (k:ℤ)*Q := hAk
      _ ≤ (2:ℤ)^L*(2:ℤ)^(L*steps (n:=n) (m:=m) r k H) :=
        mul_le_mul hkL hQP hQ.le (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hQP' : |Q| ≤ (2:ℤ)^(L*(steps (n:=n) (m:=m) r k H+1)) := by
    rw [abs_of_pos hQ]
    exact hQP.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (Nat.le_succ _)))
  change |q.num| ≤ _ ∧ (q.den:ℤ) ≤ _
  change q=(A:ℚ)/(Q:ℚ) at hA
  rw [hA]
  exact Gaussian.ratio_num_den_bound A Q hQ.ne' _ hAP hQP'

end MetricKMedian.TruncatedLP
end
end

end OAI
