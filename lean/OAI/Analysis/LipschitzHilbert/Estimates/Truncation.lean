import OAI.Analysis.LipschitzHilbert.Geometry.FrozenDirection

namespace OAI

/-! The relation between the two-sided hard cutoff and positive-time symmetrization. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

def directionalKernel (v : DirectionPlane → DirectionPlane)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) (t : ℝ) : ℂ :=
  t⁻¹ • f (sample v t x)

/-- The negative and positive parts of the original hard-truncated integral. -/
def twoSidedTruncation (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  (∫ t in -a..-ε, directionalKernel v f x t) +
    ∫ t in ε..a, directionalKernel v f x t

theorem directionalKernel_intervalIntegrable
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ} (hf : Continuous f)
    (x : DirectionPlane) (a b : ℝ) (hzero : ∀ t ∈ uIcc a b, t ≠ 0) :
    IntervalIntegrable (directionalKernel v f x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hs : Continuous (fun t : ℝ => sample v t x) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  exact (continuousOn_id.inv₀ hzero).smul (hf.comp hs).continuousOn

/-- Symmetrization is an exact identity for every positive hard inner cutoff. -/
theorem twoSidedTruncation_eq_shortTransform
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ} (hf : Continuous f)
    {ε a : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (x : DirectionPlane) :
    twoSidedTruncation v ε a f x = shortTransform v ε a f x := by
  have hp : IntervalIntegrable (directionalKernel v f x) volume ε a :=
    directionalKernel_intervalIntegrable v hf x ε a (by
      intro t ht
      rw [uIcc_of_le ha] at ht
      exact ne_of_gt (hε.trans_le ht.1))
  have hn : IntervalIntegrable (fun t => directionalKernel v f x (-t)) volume ε a := by
    have hs : Continuous (fun t : ℝ => sample v (-t) x) :=
      continuous_const.sub (continuous_id.neg.smul continuous_const)
    apply ContinuousOn.intervalIntegrable
    have hi : ContinuousOn (fun t : ℝ => (-t)⁻¹) (uIcc ε a) := by
      apply continuousOn_id.neg.inv₀
      intro t ht
      rw [uIcc_of_le ha] at ht
      exact neg_ne_zero.mpr (ne_of_gt (hε.trans_le ht.1))
    exact hi.smul (hf.comp hs).continuousOn
  unfold twoSidedTruncation shortTransform
  rw [← intervalIntegral.integral_comp_neg (directionalKernel v f x),
    ← intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directionalKernel, inv_neg, neg_smul, smul_sub]
  abel

end LipschitzHilbert

end

end OAI
