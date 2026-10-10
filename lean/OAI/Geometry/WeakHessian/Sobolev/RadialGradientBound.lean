import Mathlib
import OAI.Geometry.WeakHessian.Entropy.SobolevFisher
import OAI.Geometry.WeakHessian.LocalBounds.RadialRoots

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile39
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma normalized_radial_gradient_bounded (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hcn : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 1))
    (hs : ∀ n, Sobolev m (fun x => c n*(w x*radialCutoff o (n+k) x))) :
    ∃ M : ℝ, ∀ n, ‖(hs n).2.2.toLp (weakGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)))‖ ≤ M := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEU (n : ℕ) : IsLocalWeakUpperGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)) (Es n) := by
    simpa only [abs_of_nonneg (hcn n),Es] using (hUG (n+k)).const_mul (c n)
  have hET : Tendsto (fun n => (hEs n).toLp (Es n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
    have H := hc.smul (hDT.comp (tendsto_add_atTop_nat k))
    have he (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) :=
      (hDs (n+k)).toLp_const_smul (c n)
    simp_rw [he]
    simpa only [Function.comp_apply,one_smul] using H
  obtain ⟨M,_hM,hMb⟩ := (Metric.isBounded_range_of_tendsto (fun n => ‖(hEs n).toLp (Es n)‖) hET.norm).exists_pos_norm_le
  refine ⟨M,fun n => ?_⟩
  have H := sqrt_gradient_energy_le_upper (hs n) (hEU n) (hEs n)
  rw [← norm_toLp_sq_eq_integral (hs n).2.2,Real.sqrt_sq (norm_nonneg _)] at H
  exact H.trans (by simpa only [Real.norm_eq_abs,abs_norm] using hMb _ (mem_range_self n))
end WeakHessian

end
end InlinedFile39

end OAI
