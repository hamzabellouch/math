import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Entropy.ZeroDensity
import OAI.Geometry.WeakHessian.LocalBounds.RootApproximation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile7
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_probability_of_norm {m : Measure X} {w : X → ℝ}
    (hw : MemLp w 2 m) (hnorm : ‖hw.toLp w‖ = 1) :
    IsProbabilityMeasure (squareDensityMeasure m w) := by
  constructor
  rw [squareDensityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mp hw) (ae_of_all _ fun x => sq_nonneg (w x)),
    ← norm_toLp_sq_eq_integral hw,hnorm,one_pow,ENNReal.ofReal_one]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma normalize_root_approx {w : X → ℝ} (hw : Sobolev m w)
    (hwnorm : ‖hw.1.toLp w‖ = 1) {B : ℝ} (_hB : 0 ≤ B)
    {Q : Set X} {fs : ℕ → X → ℝ} (hLip : ∀ n, GloballyLipschitz (fs n))
    (hb : ∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B)
    (hs : ∀ n, tsupport (fs n) ⊆ Q)
    (hfs : ∀ n, MemLp (fs n) 2 m)
    {Ds : ℕ → X → ℝ} (hDs : ∀ n, MemLp (Ds n) 2 m)
    (hUG : ∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n))
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)))
    (hD : Tendsto (fun n => (hDs n).toLp (Ds n)) atTop (𝓝 (hw.2.2.toLp (weakGradient m w)))) :
    ∃ vs : ℕ → X →ᵇ ℝ, (∀ n, GloballyLipschitz (vs n)) ∧
      (∀ n x, 0 ≤ vs n x ∧ vs n x ≤ 2*B) ∧
      (∀ n, tsupport (vs n) ⊆ Q) ∧
      ∃ hvs : ∀ n, MemLp (vs n) 2 m,
      (∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n))) ∧
      ∃ Es : ℕ → X → ℝ, ∃ hEs : ∀ n, MemLp (Es n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (vs n) (Es n)) ∧
        Tendsto (fun n => (hvs n).toLp (vs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hEs n).toLp (Es n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  have hn : Tendsto (fun n => ‖(hfs n).toLp (fs n)‖) atTop (𝓝 (1:ℝ)) := by
    simpa only [hwnorm] using hF.norm
  obtain ⟨k,hk⟩ := (eventually_atTop.1 (hn.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1))))
  let c (n : ℕ) := ‖(hfs (n+k)).toLp (fs (n+k))‖⁻¹
  have hcpos (n : ℕ) : 0 < c n := inv_pos.mpr (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n)))
  have hcle (n : ℕ) : c n ≤ 2 := by
    dsimp [c]
    apply (inv_le_comm₀ (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))) (by norm_num : (0:ℝ) < 2)).mpr
    simpa using (le_of_lt (hk _ (Nat.le_add_left k n)))
  have hc : Tendsto c atTop (𝓝 (1:ℝ)) := by
    simpa only [inv_one,Function.comp_apply,c] using (hn.comp (tendsto_add_atTop_nat k)).inv₀ one_ne_zero
  let vs (n : ℕ) : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => c n*fs (n+k) x) (continuous_const.mul (hLip (n+k)).choose_spec.continuous)
    (C := 2*B) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hcpos n).le (hb (n+k) x).1)]
      exact mul_le_mul (hcle n) (hb (n+k) x).2 (hb (n+k) x).1 (by norm_num))
  let hvs (n : ℕ) : MemLp (vs n) 2 m := (hfs (n+k)).const_mul (c n)
  have hveq (n : ℕ) : (hvs n).toLp (vs n) = c n • (hfs (n+k)).toLp (fs (n+k)) := by
    exact (hfs (n+k)).toLp_const_smul (c n)
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEeq (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) := by
    exact (hDs (n+k)).toLp_const_smul (c n)
  refine ⟨vs,fun n => (hLip (n+k)).const_mul (c n),fun n x => ⟨?_,?_⟩,?_,hvs,?_,Es,hEs,?_,?_,?_⟩
  · exact mul_nonneg (hcpos n).le (hb (n+k) x).1
  · exact mul_le_mul (hcle n) (hb (n+k) x).2 (hb (n+k) x).1 (by norm_num)
  · intro n
    exact tsupport_mul_subset_right.trans (hs (n+k))
  · intro n
    apply squareDensity_probability_of_norm (hvs n)
    rw [hveq,norm_smul,Real.norm_eq_abs,abs_of_pos (hcpos n)]
    exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))))
  · intro n
    simpa only [abs_of_pos (hcpos n),vs,Es,BoundedContinuousFunction.coe_ofNormedAddCommGroup] using (hUG (n+k)).const_mul (c n)
  · simp_rw [hveq]
    simpa only [one_smul,Function.comp_apply] using hc.smul (hF.comp (tendsto_add_atTop_nat k))
  · simp_rw [hEeq]
    simpa only [one_smul,Function.comp_apply] using hc.smul (hD.comp (tendsto_add_atTop_nat k))
variable [ProperSpace X]

theorem CurvatureDimension.normalized_compact_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (hwm : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (o : X) (R : ℝ≥0) (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0) :
    ∃ vs : ℕ → X →ᵇ ℝ, (∀ n, GloballyLipschitz (vs n)) ∧
      (∀ n x, 0 ≤ vs n x ∧ vs n x ≤ 2*B) ∧
      (∀ n, tsupport (vs n) ⊆ Metric.closedBall o ((R:ℝ)+2)) ∧
      ∃ hvs : ∀ n, MemLp (vs n) 2 m,
      (∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n))) ∧
      ∃ Es : ℕ → X → ℝ, ∃ hEs : ∀ n, MemLp (Es n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (vs n) (Es n)) ∧
        Tendsto (fun n => (hvs n).toLp (vs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hEs n).toLp (Es n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  have hnorm : ‖hw.1.toLp w‖ = 1 := by
    have H := norm_toLp_sq_eq_integral hw.1
    rw [squareDensity_mass hwm] at H
    nlinarith [norm_nonneg (hw.1.toLp w)]
  obtain ⟨fs,hLip,hb,hs,hfs,Ds,hDs,hUG,hF,hD⟩ :=
    hcd.compact_root_approximation hfin hw hB hwn hwB o R hws
  exact normalize_root_approx hw hnorm hB hLip hb hs hfs hDs hUG hF hD

end WeakHessian

end
end InlinedFile7

end OAI
