import OAI.Probability.RadialTransition.ParameterTools

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma window_lipschitz {Q : Pressure} {M : ℝ} (hM : 0 ≤ M)
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (hbound : ∀ x ∈ phaseWindow (1/2), |onParameters Q x| ≤ M) :
    ∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
      |onParameters Q x-onParameters Q y| ≤ 8*M*dist x y := by
  have hnorm (x : Parameter) (hx : x ∈ phaseWindow (1/4)) (v : Parameter)
      (hv : v ∈ supportSet (onParameters Q) positiveParameters x) : ‖v‖ ≤ 8*M := by
    have hball : Metric.closedBall x (1/4) ⊆ phaseWindow (1/2) := by
      intro y hy
      convert phaseWindow_near hx hy using 1
      norm_num
    have hh := support_norm_bound (by norm_num : (0:ℝ)<1/4) hM
      (fun y hy => phaseWindow_positive (by norm_num : (1/2:ℝ)<1) (hball hy))
      (fun y hy => hbound y (hball hy)) hv
    linarith
  have hone (x : Parameter) (hx : x ∈ phaseWindow (1/4)) (y : Parameter)
      (hy : y ∈ phaseWindow (1/4)) : onParameters Q x-onParameters Q y ≤ 8*M*dist x y := by
    have hx' := phaseWindow_positive (by norm_num : (1/4:ℝ)<1) hx
    have hy' := phaseWindow_positive (by norm_num : (1/4:ℝ)<1) hy
    obtain ⟨v,hv⟩ := supportSet_nonempty isOpen_positiveParameters hQ hx'
    have hs := hv y hy'
    have hn := hnorm x hx v hv
    have hh := (real_inner_le_norm v (x-y)).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    have he : inner ℝ v (x-y) = -inner ℝ v (y-x) := by rw [← inner_neg_right, neg_sub]
    rw [he,← dist_eq_norm] at hh
    linarith
  intro x hx y hy
  rw [abs_le]
  have ha := hone x hx y hy
  have hb := hone y hy x hx
  rw [dist_comm y] at hb
  constructor <;> linarith

end RadialTransition
end

end OAI
