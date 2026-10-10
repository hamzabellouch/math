import OAI.Geometry.RCD.Harmonic.UpperLevelCaccioppoli

namespace OAI

/-! # Explicit cutoffs between two concentric closed balls -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

def nestedBallCutoff (p : X) (r s : ℝ) (x : X) : ℝ :=
  clipUnit ((s-dist p x)/(s-r))

theorem nestedBallCutoff_bounds (p : X) (r s : ℝ) (x : X) :
    0 ≤ nestedBallCutoff p r s x ∧ nestedBallCutoff p r s x ≤ 1 := clipUnit_bounds _

theorem nestedBallCutoff_eq_one (p : X) {r s : ℝ} (hrs : r < s)
    {x : X} (hx : dist p x ≤ r) : nestedBallCutoff p r s x = 1 := by
  have hd : 1 ≤ (s-dist p x)/(s-r) := (le_div_iff₀ (sub_pos.mpr hrs)).mpr (by linarith)
  simp only [nestedBallCutoff,clipUnit]
  rw [max_eq_left (by linarith),min_eq_right hd]

theorem nestedBallCutoff_eq_zero (p : X) {r s : ℝ} (hrs : r < s)
    {x : X} (hx : s ≤ dist p x) : nestedBallCutoff p r s x = 0 := by
  have hd : (s-dist p x)/(s-r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith) (sub_pos.mpr hrs).le
  simp only [nestedBallCutoff,clipUnit]
  rw [max_eq_right hd,min_eq_left zero_le_one]

theorem nestedBallCutoff_lipschitz (p : X) {r s : ℝ} (hrs : r < s) :
    LipschitzWith ⟨(s-r)⁻¹,inv_nonneg.mpr (sub_pos.mpr hrs).le⟩ (nestedBallCutoff p r s) := by
  have h := clipUnit_lipschitz.comp
    ((lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-(s-r)⁻¹)).add
      (LipschitzWith.const (s/(s-r))))
  have hc : (1:ℝ≥0)*(‖-(s-r)⁻¹‖₊*1+0) =
      ⟨(s-r)⁻¹,inv_nonneg.mpr (sub_pos.mpr hrs).le⟩ := by
    ext
    simp only [coe_nnnorm,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (inv_nonneg.mpr (sub_pos.mpr hrs).le),mul_one,one_mul,add_zero]
    rfl
  rw [hc] at h
  convert h using 1
  funext x
  dsimp only [nestedBallCutoff,Function.comp_apply]
  congr 1
  ring

theorem nestedBallCutoff_tsupport (p : X) {r s : ℝ} (hrs : r < s) :
    tsupport (nestedBallCutoff p r s) ⊆ closedBall p s := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hnot
  apply hx
  apply nestedBallCutoff_eq_zero p hrs
  have hh : ¬ dist x p ≤ s := hnot
  rw [dist_comm] at hh
  exact (lt_of_not_ge hh).le

theorem nestedBallCutoff_hasCompactSupport [ProperSpace X]
    (p : X) {r s : ℝ} (hrs : r < s) : HasCompactSupport (nestedBallCutoff p r s) :=
  (isCompact_closedBall p s).of_isClosed_subset (isClosed_tsupport _) (nestedBallCutoff_tsupport p hrs)

end RegularPointCoordinates

end

end OAI
