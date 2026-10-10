import OAI.Analysis.LipschitzHilbert.Estimates.SmoothPrincipalValue

namespace OAI

/-! Linearity of the actual symmetric principal value on smooth inputs. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

theorem shortIntegrand_intervalIntegrable
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ}
    (hf : Continuous f) {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a)
    (x : DirectionPlane) :
    IntervalIntegrable (fun t : ℝ =>
      t⁻¹ • (f (sample v t x)-f (sample v (-t) x))) volume ε a := by
  apply ContinuousOn.intervalIntegrable
  have hs : Continuous (fun t : ℝ => sample v t x) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hn : Continuous (fun t : ℝ => sample v (-t) x) :=
    continuous_const.sub (continuous_id.neg.smul continuous_const)
  apply (continuousOn_id.inv₀ ?_).smul ((hf.comp hs).sub (hf.comp hn)).continuousOn
  intro t ht
  rw [uIcc_of_le hεa] at ht
  exact (hε.trans_le ht.1).ne'

theorem shortTransform_add
    (v : DirectionPlane → DirectionPlane) {f g : DirectionPlane → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) (x : DirectionPlane) :
    shortTransform v ε a (f+g) x =
      shortTransform v ε a f x + shortTransform v ε a g x := by
  unfold shortTransform
  have heq : (fun t : ℝ => t⁻¹ •
      ((f+g) (sample v t x)-(f+g) (sample v (-t) x))) =
      (fun t : ℝ => t⁻¹ • (f (sample v t x)-f (sample v (-t) x)) +
        t⁻¹ • (g (sample v t x)-g (sample v (-t) x))) := by
    funext t
    simp only [Pi.add_apply, smul_sub, smul_add]
    abel
  rw [heq]
  exact intervalIntegral.integral_add
    (shortIntegrand_intervalIntegrable v hf hε hεa x)
    (shortIntegrand_intervalIntegrable v hg hε hεa x)

theorem shortTransform_smul
    (v : DirectionPlane → DirectionPlane) (c : ℂ)
    (f : DirectionPlane → ℂ) (ε a : ℝ) (x : DirectionPlane) :
    shortTransform v ε a (c • f) x = c • shortTransform v ε a f x := by
  unfold shortTransform
  have heq : (fun t : ℝ => t⁻¹ •
      ((c • f) (sample v t x)-(c • f) (sample v (-t) x))) =
      (fun t : ℝ => c • (t⁻¹ • (f (sample v t x)-f (sample v (-t) x)))) := by
    funext t
    simp only [Pi.smul_apply, ← smul_sub]
    exact smul_comm _ _ _
  rw [heq,intervalIntegral.integral_smul]

theorem smoothPrincipalValue_add
    (v : DirectionPlane → DirectionPlane) {f g : DirectionPlane → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {a : ℝ} (ha : 0 < a) :
    smoothPrincipalValue v a (f+g) =
      smoothPrincipalValue v a f + smoothPrincipalValue v a g := by
  funext x
  apply tendsto_nhds_unique (shortTransform_tendsto_smoothPrincipalValue v (hf.add hg) ha x)
  apply ((shortTransform_tendsto_smoothPrincipalValue v hf ha x).add
    (shortTransform_tendsto_smoothPrincipalValue v hg ha x)).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
  exact (shortTransform_add v hf.continuous hg.continuous hε hεa.le x).symm

theorem smoothPrincipalValue_smul
    (v : DirectionPlane → DirectionPlane) (c : ℂ)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) :
    smoothPrincipalValue v a (c • f) = c • smoothPrincipalValue v a f := by
  funext x
  apply tendsto_nhds_unique
    (shortTransform_tendsto_smoothPrincipalValue v (hf.const_smul c) ha x)
  apply ((shortTransform_tendsto_smoothPrincipalValue v hf ha x).const_smul c).congr'
  exact Eventually.of_forall fun ε => (shortTransform_smul v c f ε a x).symm

end LipschitzHilbert

end

end OAI
