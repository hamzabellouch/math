import OAI.MathematicalPhysics.DefocusingNLS.Profile.CompactifiedSlowDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! # Smoothness and exact jets of the compactified slow solution -/

open Set
open scoped ContDiff

namespace DefocusingNLS

noncomputable def slowAsymptoticJet (q : ℂ) (m : ℕ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => q * ((m : ℂ) - 1 - q) * slowAsymptoticJet (q + 1) m n

theorem contDiffOn_compactifiedSlowSolution (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    ContDiffOn ℝ n (compactifiedSlowSolution q m x) (Ici 0) := by
  induction n generalizing q with
  | zero =>
      exact contDiffOn_zero.mpr (continuousOn_compactifiedSlowSolution q m x hq hx hx0)
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
      refine ⟨fun t ht => (hasDerivWithinAt_compactifiedSlowSolution q m x hq hx hx0 ht).differentiableWithinAt,
        by simp, ?_⟩
      have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
      have hi : ContDiffOn ℝ n
          (fun t => q * ((m : ℂ) - 1 - q) / x * compactifiedSlowSolution (q + 1) m x t)
          (Ici 0) := contDiffOn_const.mul (ih (q + 1) hq')
      apply hi.congr
      intro t ht
      exact (hasDerivWithinAt_compactifiedSlowSolution q m x hq hx hx0 ht).derivWithin
        ((uniqueDiffOn_Ici 0) t ht)

theorem iteratedDerivWithin_compactifiedSlowSolution (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (compactifiedSlowSolution q m x) (Icc 0 1) t =
      slowAsymptoticJet q m n / x ^ n * compactifiedSlowSolution (q + n) m x t := by
  induction n generalizing q with
  | zero => simp [slowAsymptoticJet]
  | succ n ih =>
      have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
      have hd : EqOn (derivWithin (compactifiedSlowSolution q m x) (Icc 0 1))
          (fun u => q * ((m : ℂ) - 1 - q) / x * compactifiedSlowSolution (q + 1) m x u)
          (Icc 0 1) := by
        intro u hu
        exact ((hasDerivWithinAt_compactifiedSlowSolution q m x hq hx hx0 hu.1).mono
          (fun _ h => h.1)).derivWithin ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) u hu)
      rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr hd ht,
        iteratedDerivWithin_const_mul_field, ih (q + 1) hq']
      have he : q + 1 + n = q + (n + 1 : ℕ) := by push_cast; ring
      rw [he, slowAsymptoticJet, pow_succ]
      field_simp

theorem iteratedDerivWithin_compactifiedSlowSolution_zero (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    iteratedDerivWithin n (compactifiedSlowSolution q m x) (Icc 0 1) 0 =
      slowAsymptoticJet q m n / x ^ n := by
  rw [iteratedDerivWithin_compactifiedSlowSolution n q m x hq hx hx0 ⟨le_rfl, by norm_num⟩,
    compactifiedSlowSolution_zero, mul_one]

end DefocusingNLS

end OAI
