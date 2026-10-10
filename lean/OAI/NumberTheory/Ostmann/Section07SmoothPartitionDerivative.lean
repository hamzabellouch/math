import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import OAI.NumberTheory.Ostmann.Section07SmoothPartition

namespace OAI

namespace Ostmann
open scoped ContDiff

theorem smoothPartition_deriv_sub_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |deriv smoothPartition x - smoothPartition x| ≤ M := by
  have hd : Continuous (deriv smoothPartition) :=
    smoothPartition_contDiff.continuous_deriv (by simp)
  have hc : Continuous (fun x : ℝ => |deriv smoothPartition x - smoothPartition x|) :=
    (hd.sub smoothPartition_continuous).abs
  have hs : HasCompactSupport (fun x : ℝ => |deriv smoothPartition x - smoothPartition x|) :=
    (smoothPartition_hasCompactSupport.deriv.sub smoothPartition_hasCompactSupport).abs
  obtain ⟨x₀, hx₀⟩ := hc.exists_forall_ge_of_hasCompactSupport hs
  refine ⟨|deriv smoothPartition x₀ - smoothPartition x₀| + 1, by positivity, ?_⟩
  intro x
  exact (hx₀ x).trans (le_add_of_nonneg_right zero_le_one)

end Ostmann

end OAI
