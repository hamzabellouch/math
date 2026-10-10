import Mathlib
import OAI.Geometry.WeakHessian.Measure.TimeMeasure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) : Curve X :=
  ((Path.mk γ rfl rfl).trans (Path.mk η h.symm rfl)).toContinuousMap

lemma joinCurve_apply_left (γ η : Curve X) (h : γ timeOne = η timeZero)
    (t : Time) (ht : (t:ℝ) ≤ 1/2) :
    joinCurve γ η h t = evalReal γ (2*(t:ℝ)) := by
  simp only [joinCurve, Path.coe_toContinuousMap, Path.trans_apply, dite_eq_left ht,
    Path.coe_mk', evalReal]
  congr 1
  apply Subtype.ext
  simp only [clampTime]
  rw [min_eq_right (by linarith), max_eq_right (by have := t.2.1; linarith)]

lemma joinCurve_apply_right (γ η : Curve X) (h : γ timeOne = η timeZero)
    (t : Time) (ht : 1/2 ≤ (t:ℝ)) :
    joinCurve γ η h t = evalReal η (2*(t:ℝ)-1) := by
  rcases ht.eq_or_lt with heq | ht
  · rw [joinCurve_apply_left γ η h t (by linarith)]
    have he : (t:ℝ) = 1/2 := heq.symm
    simp only [he]
    norm_num [evalReal, clampTime]
    exact h
  · simp only [joinCurve, Path.coe_toContinuousMap, Path.trans_apply, dite_eq_right (not_le.mpr ht),
      Path.coe_mk', evalReal]
    change η _ = η _
    congr 1
    apply Subtype.ext
    simp only [clampTime]
    rw [min_eq_right (by have := t.2.2; linarith), max_eq_right (by linarith)]

lemma joinCurve_zero (γ η : Curve X) (h : γ timeOne = η timeZero) :
    joinCurve γ η h timeZero = γ timeZero := by
  rw [joinCurve_apply_left γ η h _ (by norm_num [timeZero])]
  simp only [evalReal, timeZero, clampTime]
  congr 1
  apply Subtype.ext
  norm_num

lemma joinCurve_one (γ η : Curve X) (h : γ timeOne = η timeZero) :
    joinCurve γ η h timeOne = η timeOne := by
  rw [joinCurve_apply_right γ η h _ (by norm_num [timeOne])]
  simp only [evalReal, timeOne, clampTime]
  congr 1
  apply Subtype.ext
  norm_num

abbrev Joinable (X : Type*) [MetricSpace X] :=
  {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}

def joinMap (p : Joinable X) : Curve X := joinCurve p.1.1 p.1.2 p.2

lemma isClosed_joinable : IsClosed {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero} :=
  isClosed_eq ((continuous_eval_const timeOne).comp continuous_fst)
    ((continuous_eval_const timeZero).comp continuous_snd)

lemma lipschitz_joinMap : LipschitzWith 1 (joinMap (X := X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  rcases le_total (t:ℝ) (1/2) with ht | ht
  · rw [joinMap, joinMap, joinCurve_apply_left _ _ _ t ht, joinCurve_apply_left _ _ _ t ht]
    exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_left _ _)
  · rw [joinMap, joinMap, joinCurve_apply_right _ _ _ t ht, joinCurve_apply_right _ _ _ t ht]
    exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_right _ _)

lemma hasControlBound_of_squareControl {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) :
    HasControlBound γ (Real.sqrt (∫ r in Icc (0:ℝ) 1, (a r)^2)) := by
  let u := ha.2.1.toLp a
  have hueq : u =ᵐ[timeMeasure] a := MemLp.coeFn_toLp ha.2.1
  have hn : ‖u‖^2 = ∫ r in Icc (0:ℝ) 1, (a r)^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hueq] with r hr
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hr]
  refine ⟨u, ?_, fun s t hst => ?_⟩
  · rw [← hn, Real.sqrt_sq (norm_nonneg u)]
  · rw [intervalFunctional_apply s t u hst]
    have heq : (∫ r in (s:ℝ)..(t:ℝ), u r) = ∫ r in (s:ℝ)..(t:ℝ), a r := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (show (s:ℝ) ≤ (t:ℝ) from hst)]
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.2.1 t.2.2)) hueq
    rw [heq]
    exact ha.2.2.2 s t hst

end WeakHessian

open Set MeasureTheory Filter
open scoped ENNReal NNReal

end
end InlinedFile0

end OAI
