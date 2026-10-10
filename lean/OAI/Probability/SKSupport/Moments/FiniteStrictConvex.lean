import Mathlib
import OAI.Probability.SKSupport.Parabolic.AffineEvolution

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma softAbs_curvature_pos {M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < deriv (deriv (softAbs M)) x := by
  have he : deriv (softAbs M) = fun y => Real.tanh (M*y) :=
    funext (fun y => (hasDerivAt_softAbs (ne_of_gt hM) y).deriv)
  rw [he]
  have hd := (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd' : HasDerivAt (fun y => Real.tanh (M*y)) ((1-(Real.tanh (M*x))^2)*M) x := by
    simpa only [Function.comp_def,id_eq,mul_one] using hd
  rw [hd'.deriv]
  have hh := Real.abs_tanh_lt_one (M*x)
  have hs : (Real.tanh (M*x))^2 < 1 := by nlinarith [sq_abs (Real.tanh (M*x)),abs_nonneg (Real.tanh (M*x))]
  exact mul_pos (sub_pos.mpr hs) hM

lemma cascade_curvature_pos {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hpos : ∀ x, 0 < deriv (deriv f) x) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (x : ℝ) :
    0 < deriv (deriv (cascade c h f N i)) x := by
  induction N generalizing i x with
  | zero => exact hpos x
  | succ N ih =>
    exact logSemigroup_curvature_pos (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (ih (i+1)) (c i).coe_nonneg h x

lemma varianceLogHeat_curvature_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hpos : ∀ x, 0 < deriv (deriv f) x)
    {c : ℝ} (hc : 0 ≤ c) (t x : ℝ) :
    0 < deriv (deriv (varianceLogHeat c t f)) x := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact logSemigroup_curvature_pos hf hLip hpos hc _ x

theorem finite_softAbs_curvature_pos {M : ℝ} (hM : 0 < M)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t x : ℝ) :
    0 < deriv (deriv (finiteValue c h (softAbs M) N i t)) x := by
  induction N generalizing i t with
  | zero => exact softAbs_curvature_pos hM x
  | succ N ih =>
    by_cases ht : t ≤ h
    · rw [finiteValue_head _ c h N i ht]
      exact varianceLogHeat_curvature_pos
        (cascade_regular (regularDatum_softAbs (ne_of_gt hM)) (softAbs_lipschitz (ne_of_gt hM)) c h N (i+1))
        (cascade_lipschitz (softAbs_lipschitz (ne_of_gt hM)) c h N (i+1))
        (cascade_curvature_pos (regularDatum_softAbs (ne_of_gt hM)) (softAbs_lipschitz (ne_of_gt hM))
          (softAbs_curvature_pos hM) c h N (i+1)) (c i).coe_nonneg (h-t) x
    · rw [finiteValue_tail _ c h N i (lt_of_not_ge ht)]
      exact ih (i+1) (t-h)

end ZeroTemperatureSK.Heat

end
end

end OAI
