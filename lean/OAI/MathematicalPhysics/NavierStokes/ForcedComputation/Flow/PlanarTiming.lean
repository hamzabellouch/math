import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles

namespace OAI

/-! Rational disjoint pulse slots for a finite planar instruction list. -/

noncomputable section

namespace ForcedComputation.PlanarTiming

open ShearFlows Set
open scoped ContDiff

def start {n : ℕ} (k : Fin n) : ℚ := (2 * (k.val : ℚ) + 1) / (2 * ((n : ℚ) + 1))

def finish {n : ℕ} (k : Fin n) : ℚ := (2 * (k.val : ℚ) + 2) / (2 * ((n : ℚ) + 1))

theorem intervals {n : ℕ} (k : Fin n) :
    0 < start k ∧ start k < finish k ∧ finish k < 1 := by
  have hn : (0 : ℚ) < 2 * (n + 1) := by positivity
  have hk : (k.val : ℚ) < n := by exact_mod_cast k.isLt
  refine ⟨by unfold start; positivity, ?_, ?_⟩
  · unfold start finish
    exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)
  · unfold finish
    exact (div_lt_one hn).mpr (by linarith)

theorem ordered {n : ℕ} {i j : Fin n} (hij : i < j) : finish i < start j := by
  have hn : (0 : ℚ) < 2 * (n + 1) := by positivity
  have hi : (i.val : ℚ) + 1 ≤ j.val := by exact_mod_cast hij
  unfold start finish
  exact (div_lt_div_iff_of_pos_right hn).mpr (by linarith)

def clock {n : ℕ} (k : Fin n) : ℝ → ℝ := smoothRamp (start k) (finish k)

def pulse {n : ℕ} (k : Fin n) : ℝ → ℝ := smoothPulse (start k) (finish k)

theorem clock_smooth {n : ℕ} (k : Fin n) : ContDiff ℝ ∞ (clock k) := smoothRamp_smooth _ _

theorem pulse_smooth {n : ℕ} (k : Fin n) : ContDiff ℝ ∞ (pulse k) := smoothPulse_smooth _ _

theorem clock_derivative {n : ℕ} (k : Fin n) (t : ℝ) : HasDerivAt (clock k) (pulse k t) t :=
  ((clock_smooth k).differentiable (by simp) t).hasDerivAt

theorem clock_range {n : ℕ} (k : Fin n) (t : ℝ) : clock k t ∈ Icc (0 : ℝ) 1 :=
  smoothRamp_range _ _ _

theorem clock_at_zero {n : ℕ} (k : Fin n) : clock k 0 = 0 :=
  smoothRamp_before (by exact_mod_cast (intervals k).2.1)
    (by exact_mod_cast (intervals k).1.le)

theorem clock_at_one {n : ℕ} (k : Fin n) : clock k 1 = 1 :=
  smoothRamp_after (by exact_mod_cast (intervals k).2.1)
    (by exact_mod_cast (intervals k).2.2.le)

theorem pulse_active {n : ℕ} {k : Fin n} {t : ℝ} (ht : pulse k t ≠ 0) :
    (start k : ℝ) < t ∧ t < finish k := by
  have ho : (start k : ℝ) < finish k := by exact_mod_cast (intervals k).2.1
  exact ⟨lt_of_not_ge (fun h => ht (smoothPulse_before ho h)),
    lt_of_not_ge (fun h => ht (smoothPulse_after ho h))⟩

theorem active_previous {n : ℕ} {i j : Fin n} {t : ℝ}
    (hij : i < j) (ht : pulse j t ≠ 0) : clock i t = 1 ∧ pulse i t = 0 := by
  have ho : (start i : ℝ) < finish i := by exact_mod_cast (intervals i).2.1
  have hg : (finish i : ℝ) < start j := by exact_mod_cast ordered hij
  have hi : (finish i : ℝ) ≤ t := (hg.trans (pulse_active ht).1).le
  exact ⟨smoothRamp_after ho hi, smoothPulse_after ho hi⟩

theorem active_future {n : ℕ} {i j : Fin n} {t : ℝ}
    (hij : i < j) (ht : pulse i t ≠ 0) : clock j t = 0 ∧ pulse j t = 0 := by
  have ho : (start j : ℝ) < finish j := by exact_mod_cast (intervals j).2.1
  have hg : (finish i : ℝ) < start j := by exact_mod_cast ordered hij
  have hj : t ≤ (start j : ℝ) := ((pulse_active ht).2.trans hg).le
  exact ⟨smoothRamp_before ho hj, smoothPulse_before ho hj⟩

theorem pulse_unique {n : ℕ} {i j : Fin n} {t : ℝ}
    (hi : pulse i t ≠ 0) (hj : pulse j t ≠ 0) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj (active_future h hi).2)
  · exact h
  · exact False.elim (hi (active_future h hj).2)

end ForcedComputation.PlanarTiming

end

end OAI
