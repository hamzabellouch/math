import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicExpressions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! Periodization preserves a sup bound when the support is shorter than
one period: at any point, at most one translated copy contributes. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem iteratedDeriv_support_interval {f : ℝ → ℝ} {a b : ℝ}
    (hs : Function.support f ⊆ Icc a b) (n : ℕ) :
    Function.support (iteratedDeriv n f) ⊆ Icc a b := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hs
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact support_deriv_subset.trans (closure_minimal ih isClosed_Icc)

theorem iteratedDeriv_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem periodize_iteratedDeriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Icc a b) (n : ℕ) :
    iteratedDeriv n (periodize 1 f) = periodize 1 (iteratedDeriv n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih,
      periodize_deriv (by norm_num : (0 : ℝ) < 1) (iteratedDeriv_support_interval hs n)
        (iteratedDeriv_smooth hf n), iteratedDeriv_succ]

theorem periodize_unit_bound {f : ℝ → ℝ} {a b B : ℝ}
    (hs : Function.support f ⊆ Icc a b) (hlen : b - a < 1)
    (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (x : ℝ) :
    |periodize 1 f x| ≤ B := by
  classical
  by_cases hex : ∃ n : ℤ, f (x - (n : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hex
    have hu (m : ℤ) (hm : m ≠ n) : f (x - (m : ℝ)) = 0 := by
      by_contra hfm
      have hsn := hs hn
      have hsm := hs hfm
      rcases lt_or_gt_of_ne hm with hm | hm
      · have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Int.add_one_le_iff.mpr hm)
        linarith [hsn.1, hsm.2]
      · have hc : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Int.add_one_le_iff.mpr hm)
        linarith [hsm.1, hsn.2]
    have he : periodize 1 f x = f (x - (n : ℝ)) := by
      unfold periodize
      simpa only [one_mul] using (tsum_eq_single n (fun m hm => by
        simpa only [one_mul] using hu m hm))
    rw [he]
    exact hb _
  · have he : periodize 1 f x = 0 := by
      change (∑' n : ℤ, f (x - 1 * (n : ℝ))) = 0
      trans (∑' _ : ℤ, (0 : ℝ))
      swap
      · exact tsum_zero
      apply tsum_congr
      intro n
      simpa only [one_mul, ne_eq, not_not] using (not_exists.mp hex n)
    rw [he, abs_zero]
    exact hB

end ForcedComputation.VelocityDetector

end

end OAI
