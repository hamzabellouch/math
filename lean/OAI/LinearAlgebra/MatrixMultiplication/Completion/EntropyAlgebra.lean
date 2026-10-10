import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionEntropyAlgebra

open MatrixMultiplication.Foundation

def binaryEntropy (a : ℝ) : ℝ := entropyTerm a + entropyTerm (1 - a)

def conditionalMixEntropy (a : ℝ) (m : ℕ) (Hc Ho : ℝ) : ℝ :=
  ((m : ℝ) * (binaryEntropy a + a * Hc + (1 - a) * Ho) -
    binaryEntropy (a ^ m) - a ^ m * ((m : ℝ) * Hc)) / (1 - a ^ m)

theorem conditionalMixEntropy_eq_split (a : ℝ) (m : ℕ) (Hc Ho : ℝ)
    (hden : 1 - a ^ m ≠ 0) :
    conditionalMixEntropy a m Hc Ho =
      ((m : ℝ) * (binaryEntropy a + a * Hc + (1 - a) * Ho) -
        entropyTerm (a ^ m) - a ^ m * ((m : ℝ) * Hc)) / (1 - a ^ m) +
        Real.log (1 - a ^ m) := by
  dsimp [conditionalMixEntropy, binaryEntropy, entropyTerm]
  field_simp
  ring

private theorem conditionalMixEntropy_cancel
    (a C O L hc ho : ℝ) (m : ℕ)
    (hden : 1 - a ^ m ≠ 0)
    (hcLog : Real.log a = C - L)
    (hoLog : Real.log (1 - a) = O - L) :
    conditionalMixEntropy a m (C + hc) (O + ho) =
      m * L + Real.log (1 - a ^ m) +
        m * ((a - a ^ m) / (1 - a ^ m) * hc +
          (1 - a) / (1 - a ^ m) * ho) := by
  dsimp [conditionalMixEntropy, binaryEntropy, entropyTerm]
  rw [Real.log_pow, hcLog, hoLog]
  field_simp
  ring

private theorem ratio_range (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < x / (x + y) ∧ x / (x + y) < 1 := by
  have hs : 0 < x + y := add_pos hx hy
  exact ⟨div_pos hx hs, (div_lt_one hs).mpr (by linarith)⟩

private theorem ratio_complement (x y : ℝ) (h : x + y ≠ 0) :
    1 - x / (x + y) = y / (x + y) := by
  field_simp
  exact add_sub_cancel_left x y

theorem binaryEntropy_cardinal_mixture (np nq : ℝ) (hnp : 0 < np) (hnq : 0 < nq) :
    let a := np / (np + nq)
    binaryEntropy a + a * Real.log np + (1 - a) * Real.log nq =
      Real.log (np + nq) := by
  let a := np / (np + nq)
  have hs : 0 < np + nq := add_pos hnp hnq
  have hcLog : Real.log a = Real.log np - Real.log (np + nq) :=
    Real.log_div hnp.ne' hs.ne'
  have hoLog : Real.log (1 - a) = Real.log nq - Real.log (np + nq) := by
    rw [show 1 - a = nq / (np + nq) from ratio_complement np nq hs.ne',
      Real.log_div hnq.ne' hs.ne']
  change binaryEntropy a + a * Real.log np + (1 - a) * Real.log nq = _
  dsimp [binaryEntropy, entropyTerm]
  rw [hcLog, hoLog]
  ring

theorem conditionalMixEntropy_incident
    (np nq hc ho : ℝ) (m : ℕ)
    (hnp : 0 < np) (hnq : 0 < nq) (hm : 0 < m) :
    let a := np / (np + nq)
    conditionalMixEntropy a m (Real.log np + hc) (Real.log nq + ho) -
        Real.log ((np + nq) ^ m - np ^ m) =
      m * ((a - a ^ m) / (1 - a ^ m) * hc +
        (1 - a) / (1 - a ^ m) * ho) := by
  let a := np / (np + nq)
  change conditionalMixEntropy a m (Real.log np + hc) (Real.log nq + ho) -
      Real.log ((np + nq) ^ m - np ^ m) = _
  have hs : 0 < np + nq := add_pos hnp hnq
  have ha : 0 < a ∧ a < 1 := ratio_range np nq hnp hnq
  have hden : 0 < 1 - a ^ m :=
    sub_pos.mpr (pow_lt_one₀ ha.1.le ha.2 (Nat.ne_of_gt hm))
  have hcLog : Real.log a = Real.log np - Real.log (np + nq) :=
    Real.log_div hnp.ne' hs.ne'
  have hoLog : Real.log (1 - a) = Real.log nq - Real.log (np + nq) := by
    rw [show 1 - a = nq / (np + nq) from ratio_complement np nq hs.ne',
      Real.log_div hnq.ne' hs.ne']
  have hfactor : (np + nq) ^ m - np ^ m =
      (np + nq) ^ m * (1 - a ^ m) := by
    dsimp [a]
    rw [div_pow]
    field_simp
  have hlog : Real.log ((np + nq) ^ m - np ^ m) =
      m * Real.log (np + nq) + Real.log (1 - a ^ m) := by
    rw [hfactor, Real.log_mul (pow_ne_zero _ hs.ne') hden.ne', Real.log_pow]
  rw [conditionalMixEntropy_cancel a (Real.log np) (Real.log nq)
    (Real.log (np + nq)) hc ho m hden.ne' hcLog hoLog, hlog]
  ring

theorem conditionalMixEntropy_gibbs (q hc ho : ℝ) (m : ℕ) (hm : 0 < m) :
    conditionalMixEntropy (Real.exp hc / (Real.exp hc + Real.exp ho)) m
        (Real.log q + hc) (Real.log q + ho) - m * Real.log q =
      Real.log ((Real.exp hc + Real.exp ho) ^ m - Real.exp ((m : ℝ) * hc)) := by
  let a := Real.exp hc / (Real.exp hc + Real.exp ho)
  have ha : 0 < a ∧ a < 1 := ratio_range _ _ (Real.exp_pos hc) (Real.exp_pos ho)
  have hden : 1 - a ^ m ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ ha.1.le ha.2 (Nat.ne_of_gt hm))).ne'
  have hmean : m * ((a - a ^ m) / (1 - a ^ m) * Real.log q +
      (1 - a) / (1 - a ^ m) * Real.log q) = m * Real.log q := by
    field_simp
    ring
  have h := conditionalMixEntropy_incident (Real.exp hc) (Real.exp ho)
    (Real.log q) (Real.log q) m (Real.exp_pos hc) (Real.exp_pos ho) hm
  change conditionalMixEntropy a m (Real.log (Real.exp hc) + Real.log q)
      (Real.log (Real.exp ho) + Real.log q) -
      Real.log ((Real.exp hc + Real.exp ho) ^ m - Real.exp hc ^ m) =
        m * ((a - a ^ m) / (1 - a ^ m) * Real.log q +
          (1 - a) / (1 - a ^ m) * Real.log q) at h
  rw [Real.log_exp, Real.log_exp, add_comm hc (Real.log q),
    add_comm ho (Real.log q), hmean, ← Real.exp_nat_mul hc m] at h
  change conditionalMixEntropy a m (Real.log q + hc) (Real.log q + ho) -
      m * Real.log q = _
  linarith

end MatrixMultiplication.CompletionEntropyAlgebra

end

end OAI
