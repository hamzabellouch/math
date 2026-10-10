import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroQuotientGrowth
import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeVanishing
import OAI.NumberTheory.Ostmann.ZeroDensity.LogarithmicDiskRate

namespace OAI

/-! # Constant logarithmic derivative after removing a finite zero set -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology BigOperators

/-- The precise elementary finite-order consequence needed for a hypothetical
finite set of completed-character zeros. -/
theorem finite_zero_quotient_logDeriv_constant (f g : ℂ → ℂ) (S : Finset ℂ)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (he : ∀ z, f z = finiteZeroPolynomial f S z * g z)
    (A : ℝ) (hA : 0 < A)
    (hf : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖f z‖ ≤ A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3))) :
    ∃ c : ℂ, ∀ z, logDeriv g z = c := by
  obtain ⟨R, hR⟩ := exists_nat_gt (∑ z ∈ S, ‖z‖)
  have hS : ∀ z ∈ S, ‖z‖ ≤ (R : ℝ) := by
    intro z hz
    exact (Finset.single_le_sum (fun w _ => norm_nonneg w) hz).trans hR.le
  have hgrowth := finite_zero_quotient_log_growth f g S R hS A hA hg hne he hf
  have hderiv : ∀ w, deriv (logDeriv g) w = 0 := by
    intro w
    obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    let b : ℝ := (m : ℝ) + R + 4
    let D : ℝ := |Real.log ‖g w‖| + 1
    let B : ℕ → ℝ := fun n => A * ((n : ℝ) + b) * (1 + Real.log ((n : ℝ) + b)) + D
    have hb : 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) R]
    have hB (n : ℕ) : 0 < B n := by
      have hl : 0 ≤ Real.log ((n : ℝ) + b) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
      dsimp [B, D]
      positivity
    have hlocal : ∀ (n : ℕ) (z : ℂ), z ∈ ball (0 : ℂ) ((n : ℝ) + 1) →
        Real.log ‖g (z + w)‖ - Real.log ‖g (0 + w)‖ ≤ B n := by
      intro n z hz
      have hzn : ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball, dist_zero_right] using hz
      have hzw : ‖z + w‖ ≤ ((n + m : ℕ) : ℝ) + 1 := by
        have hh := norm_add_le z w
        push_cast
        linarith
      have hh := hgrowth (n + m) (z + w) hzw
      simp only [Nat.cast_add] at hh
      dsimp [B, b, D]
      simp only [zero_add]
      simp only [add_assoc] at hh ⊢
      linarith [neg_le_abs (Real.log ‖g w‖)]
    have hh := deriv_logDeriv_eq_zero_of_disk_bounds (fun z => g (z + w))
      (fun z => (hg (z + w)).comp (f := fun u : ℂ => u + w) (x := z) (by fun_prop))
      (fun z => hne (z + w)) (fun n => (n : ℝ) + 1) B (fun _ => by positivity) hB hlocal
      (logarithmic_disk_rate A b D hb)
    have hshift : logDeriv (fun z => g (z + w)) = fun z => logDeriv g (z + w) := by
      funext z
      have hc := logDeriv_comp (f := g) (g := fun u : ℂ => u + w) (x := z)
        (hg (z + w)).differentiableAt (differentiableAt_id.add_const w)
      simpa [Function.comp_def] using hc
    rw [hshift, deriv_comp_add_const, zero_add] at hh
    exact hh
  have hd : Differentiable ℂ (logDeriv g) := fun z =>
    ((hg z).deriv.div (hg z) (hne z)).differentiableAt
  refine ⟨logDeriv g 0, fun z => ?_⟩
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    hd.differentiableOn (fun w _ => hderiv w) (mem_univ z) (mem_univ 0)

end Ostmann

end OAI
