import OAI.Analysis.LipschitzHilbert.Estimates.ExponentialVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! The actual logarithmic weights and their full-root variation estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def hierarchyLog (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (k : ℕ) : ℂ :=
  ((-a * Real.log (n k) : ℝ) : ℂ) - ∑ i ∈ Finset.range k, z i * (R i : ℂ)

def hierarchyWeight (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (hierarchyLog n R z a k)

theorem hierarchyLog_re_le (n R : ℕ → ℝ) (z : ℕ → ℂ) (a h : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hh : 0 < h) (hn : h ≤ n k)
    (hR : ∀ i < k, 0 ≤ R i) (hz : ∀ i < k, 0 ≤ (z i).re) :
    (hierarchyLog n R z a k).re ≤ -a * Real.log h := by
  have hlog : Real.log h ≤ Real.log (n k) := Real.log_le_log hh hn
  have hsum : 0 ≤ ∑ i ∈ Finset.range k, (z i).re * R i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hz i (Finset.mem_range.mp hi))
      (hR i (Finset.mem_range.mp hi)))
  simp only [hierarchyLog, Complex.sub_re, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

theorem hierarchyWeight_norm_le (n R : ℕ → ℝ) (z : ℕ → ℂ) (a h : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hh : 0 < h) (hn : h ≤ n k)
    (hR : ∀ i < k, 0 ≤ R i) (hz : ∀ i < k, 0 ≤ (z i).re) :
    ‖hierarchyWeight n R z a k‖ ≤ h ^ (-a) := by
  rw [hierarchyWeight, Complex.norm_exp, Real.rpow_def_of_pos hh]
  have heq : Real.log h * -a = -a * Real.log h := mul_comm _ _
  rw [heq]
  exact Real.exp_le_exp.mpr (hierarchyLog_re_le n R z a h k ha hh hn hR hz)

theorem hierarchyLog_increment (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (k : ℕ)
    (hn : 0 < n k) (hn' : 0 < n (k + 1)) :
    hierarchyLog n R z a (k + 1) - hierarchyLog n R z a k =
      ((a * Real.log (n k / n (k + 1)) : ℝ) : ℂ) - z k * (R k : ℂ) := by
  rw [hierarchyLog, hierarchyLog, Finset.sum_range_succ, Real.log_div hn.ne' hn'.ne']
  push_cast
  ring

theorem hierarchyWeight_variation (n R : ℕ → ℝ) (z : ℕ → ℂ)
    (N K : ℕ) (a h Z : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, h ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j + 1 - K) / n (j + 1)))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖hierarchyWeight n R z a N‖ +
      (∑ j ∈ Finset.range N, ‖hierarchyWeight n R z a (j + 1) - hierarchyWeight n R z a j‖) ≤
      h ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  have hn0 : ∀ j ≤ N, 0 < n j := fun j hj => hh.trans_le (hn j hj)
  have hbound (j : ℕ) (hj : j ≤ N) : (hierarchyLog n R z a j).re ≤ -a * Real.log h :=
    hierarchyLog_re_le n R z a h j ha hh (hn j hj)
      (fun i hi => hR0 i (hi.trans_le hj)) (fun i hi => hz0 i (hi.trans_le hj))
  have hinc (j : ℕ) (hj : j < N) := hierarchyLog_increment n R z a j
    (hn0 j (by omega)) (hn0 (j + 1) (by omega))
  have hvariation := exponential_hierarchy_variation (hierarchyLog n R z a) n R z
    N K a (-a * Real.log h) Z hn0 hmono hR0 hR ha hZ hz hbound hinc
  have heq : Real.exp (-a * Real.log h) = h ^ (-a) := by
    rw [Real.rpow_def_of_pos hh, mul_comm]
  simpa only [hierarchyWeight, heq] using hvariation

end LipschitzHilbert

end

end OAI
