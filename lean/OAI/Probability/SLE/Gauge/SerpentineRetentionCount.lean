import OAI.Probability.SLE.Gauge.SerpentineParameters

namespace OAI

/-! All selected integer strips occur strictly before the rounded
completion, with exactly m² distinct selected steps. -/

noncomputable section
open Set

namespace SLEExactGauge.Serpentine

lemma retainedStep_pos (A : ℝ) (m j i : ℕ) : 0 < retainedStep A m j i := by
  unfold retainedStep
  omega

lemma retainedStep_lt_completion {A : ℝ} (hA : 0 ≤ A) {m j i : ℕ}
    (hm : 0 < m) (hj : j < m) (hi : i < m) :
    retainedStep A m j i < completionStep A m := by
  have hupper := (retainedStep_bounds (j := j) hA hi).2
  have hsep := columnEntry_separation (A := A) hm (show j < 2 * m by omega)
  have hceil := Nat.le_ceil (columnEntry A m (2 * m) + 200 * (m : ℝ))
  change columnEntry A m (2 * m) + 200 * (m : ℝ) ≤ (completionStep A m : ℝ) at hceil
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : (retainedStep A m j i : ℝ) < completionStep A m := by linarith
  exact_mod_cast hr

theorem retainedSteps_bounds {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m) :
    ∀ k ∈ retainedSteps A m, 0 < k ∧ k < completionStep A m := by
  intro k hk
  obtain ⟨⟨j, i⟩, _, rfl⟩ := Finset.mem_image.mp hk
  exact ⟨retainedStep_pos A m j i, retainedStep_lt_completion hA hm j.isLt i.isLt⟩

end SLEExactGauge.Serpentine

end

end OAI
