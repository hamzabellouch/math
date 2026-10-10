import OAI.NumberTheory.JointDickman.Amplification.RampDensityIntegral
import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityRegularity

namespace OAI

/-! # Bounded Lipschitz densities after the lower ramp cutoff -/

namespace JointDickman

open scoped NNReal

noncomputable def rampDensity (f : ℝ → ℝ) (lo hi x : ℝ) : ℝ :=
  averagingRamp lo hi x * f (max lo x)

theorem rampDensity_zero (f : ℝ → ℝ) {lo hi x : ℝ} (hlohi : lo < hi) (hx : x ≤ lo) :
    rampDensity f lo hi x = 0 := by
  simp only [rampDensity, averagingRamp_zero hlohi hx, zero_mul]

theorem rampDensity_eq (f : ℝ → ℝ) {lo hi x : ℝ} (hx : lo ≤ x) :
    rampDensity f lo hi x = averagingRamp lo hi x * f x := by
  simp only [rampDensity, max_eq_right hx]

theorem rampDensity_bound (f : ℝ → ℝ) {lo hi M : ℝ} (hlohi : lo < hi)
    (hbound : ∀ x ∈ Set.Ici lo, |f x| ≤ M) (x : ℝ) :
    |rampDensity f lo hi x| ≤ M := by
  have hr := averagingRamp_bounds hlohi x
  have hf := hbound (max lo x) (Set.mem_Ici.mpr (le_max_left _ _))
  rw [rampDensity, abs_mul, abs_of_nonneg hr.1]
  exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans (by simpa using hf)

theorem clampedDensity_lipschitz (f : ℝ → ℝ) {lo : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L f (Set.Ici lo)) :
    LipschitzWith L (fun x => f (max lo x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hLip.dist_le_mul (max lo x) (Set.mem_Ici.mpr (le_max_left lo x))
    (max lo y) (Set.mem_Ici.mpr (le_max_left lo y))
  have hm : dist (max lo x) (max lo y) ≤ dist x y := by
    simpa only [id_eq, NNReal.coe_one, one_mul] using (LipschitzWith.id.const_max lo).dist_le_mul x y
  exact h.trans (mul_le_mul_of_nonneg_left hm L.coe_nonneg)

theorem rampDensity_lipschitz (f : ℝ → ℝ) {lo hi : ℝ} {M L : ℝ≥0}
    (hlohi : lo < hi) (hbound : ∀ x ∈ Set.Ici lo, |f x| ≤ M)
    (hLip : LipschitzOnWith L f (Set.Ici lo)) :
    LipschitzWith ⟨(L : ℝ) + (1 / (hi - lo)) * (M : ℝ), by positivity⟩ (rampDensity f lo hi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hrx := averagingRamp_bounds hlohi x
  have hrd := (averagingRamp_lipschitz hlohi).dist_le_mul x y
  have hfd := (clampedDensity_lipschitz f hLip).dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at hrd hfd
  have hfy := hbound (max lo y) (Set.mem_Ici.mpr (le_max_left _ _))
  change |rampDensity f lo hi x - rampDensity f lo hi y| ≤
    ((L : ℝ) + (1 / (hi - lo)) * (M : ℝ)) * |x - y|
  calc
    _ = |averagingRamp lo hi x * (f (max lo x) - f (max lo y)) +
      (averagingRamp lo hi x - averagingRamp lo hi y) * f (max lo y)| := by
        unfold rampDensity
        congr 1
        ring
    _ ≤ |averagingRamp lo hi x * (f (max lo x) - f (max lo y))| +
      |(averagingRamp lo hi x - averagingRamp lo hi y) * f (max lo y)| := abs_add_le _ _
    _ ≤ (L : ℝ) * |x - y| + ((1 / (hi - lo)) * |x - y|) * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg hrx.1]
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right hrx.2 (abs_nonneg _)).trans (by simpa using hfd)
      · exact mul_le_mul hrd hfy (abs_nonneg _) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
