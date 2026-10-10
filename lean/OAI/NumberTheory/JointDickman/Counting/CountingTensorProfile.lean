import OAI.NumberTheory.JointDickman.Counting.CountingRamp
import OAI.NumberTheory.JointDickman.Arithmetic.WeightedSmoothFeatures
import OAI.NumberTheory.JointDickman.Probability.AmplificationTensorProfile

namespace OAI

/-! # The continuous profile for the counting-scale restriction -/

namespace JointDickman
open scoped Topology

noncomputable def countingTensorProfile (δ : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  amplificationSpatialProfile (v 0) (v 1) (v 2)*countingRamp δ (v 3) (v 1/v 2)

noncomputable def countingBoxWeight (B : ℕ) (δ s σ x y z : ℝ) : ℝ :=
  amplificationBoxWeight B s x y z*countingRamp δ σ (y/z)

theorem countingTensorProfile_continuous {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (countingTensorProfile δ) tensorParameterBox := by
  have hv (i : Fin 4) : ContinuousOn (fun v : Fin 4 → ℝ => v i) tensorParameterBox :=
    (continuous_apply i).continuousOn
  have hz : ∀ v ∈ tensorParameterBox, v 2 ≠ 0 := by
    intro v hv
    have hh : (1/4 : ℝ) ≤ v 2 := hv.1 2
    linarith
  have hp := ((amplificationBump.continuous.comp_continuousOn ((hv 0).div (hv 2) hz)).mul
    (amplificationBump.continuous.comp_continuousOn ((hv 1).div (hv 2) hz))).mul
    (dyadicPartitionWeight_smooth.continuous.comp_continuousOn (hv 2))
  exact hp.mul ((countingRamp_continuous hδ).comp_continuousOn
    ((hv 3).prodMk ((hv 1).div (hv 2) hz)))

theorem countingTensorProfile_cutoff (δ σ x y z : ℝ) :
    countingTensorProfile δ ![x,y,z,σ]*tensorCutoff x y z =
      amplificationSpatialProfile x y z*countingRamp δ σ (y/z) := by
  change (amplificationSpatialProfile x y z*countingRamp δ σ (y/z))*tensorCutoff x y z = _
  by_cases h : amplificationSpatialProfile x y z = 0
  · simp only [h,zero_mul]
  · rw [amplificationSpatialProfile_cutoff h,mul_one]

theorem countingBoxWeight_freezing {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 0 < B → ∀ s σ x y z : ℝ,
      |countingBoxWeight B δ s σ x y z-
        amplificationBump s*(countingTensorProfile δ ![x,y,z,σ]*tensorCutoff x y z)| ≤
        (C/B)*tensorCutoff x y z := by
  obtain ⟨C,hC,hfreeze⟩ := amplificationBoxWeight_freezing
  refine ⟨C,hC,?_⟩
  intro B hB s σ x y z
  rw [countingTensorProfile_cutoff]
  change |amplificationBoxWeight B s x y z*countingRamp δ σ (y/z)-
    amplificationBump s*(amplificationSpatialProfile x y z*countingRamp δ σ (y/z))| ≤ _
  have he : amplificationBoxWeight B s x y z*countingRamp δ σ (y/z)-
      amplificationBump s*(amplificationSpatialProfile x y z*countingRamp δ σ (y/z)) =
      (amplificationBoxWeight B s x y z-amplificationTensorProfile ![x,y,z,s])*
        countingRamp δ σ (y/z) := by
        change _ = (amplificationBoxWeight B s x y z-amplificationBump s*amplificationSpatialProfile x y z)*_
        ring
  rw [he,abs_mul,abs_of_nonneg (countingRamp_bounds hδ σ (y/z)).1]
  exact (mul_le_mul_of_nonneg_left (countingRamp_bounds hδ σ (y/z)).2 (abs_nonneg _)).trans
    (by simpa only [mul_one] using hfreeze B hB s x y z)

end JointDickman

end OAI
