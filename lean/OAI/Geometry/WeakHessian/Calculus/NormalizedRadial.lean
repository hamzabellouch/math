import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormalizedRoots
import OAI.Geometry.WeakHessian.LocalBounds.RadialRoots

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile29
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_probability_normalization {w : X → ℝ} (hw : MemLp w 2 m)
    (hwm : Measurable w) [IsProbabilityMeasure (squareDensityMeasure m w)] (o : X) :
    ∃ k : ℕ, ∃ c : ℕ → ℝ, (∀ n, 0 < c n ∧ c n ≤ 2) ∧ Tendsto c atTop (𝓝 1) ∧
      ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))) := by
  have hnorm : ‖hw.toLp w‖ = 1 := by
    have H := norm_toLp_sq_eq_integral hw
    rw [squareDensity_mass hwm] at H
    nlinarith [norm_nonneg (hw.toLp w)]
  have hn : Tendsto (fun n => ‖(radial_mul_memLp hw o n).toLp (fun x => w x*radialCutoff o n x)‖)
      atTop (𝓝 (1:ℝ)) := by simpa only [hnorm] using (radial_mul_tendsto hw o).norm
  obtain ⟨k,hk⟩ := eventually_atTop.1 (hn.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let c (n : ℕ) := ‖(radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x)‖⁻¹
  have hpos (n : ℕ) : 0 < ‖(radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x)‖ :=
    lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))
  have hc (n : ℕ) : 0 < c n ∧ c n ≤ 2 := by
    refine ⟨inv_pos.mpr (hpos n),?_⟩
    exact (inv_le_comm₀ (hpos n) (by norm_num : (0:ℝ)<2)).mpr (by simpa using (hk _ (Nat.le_add_left k n)).le)
  refine ⟨k,c,hc,?_,?_⟩
  · simpa only [inv_one,Function.comp_apply,c] using (hn.comp (tendsto_add_atTop_nat k)).inv₀ one_ne_zero
  · intro n
    apply squareDensity_probability_of_norm ((radial_mul_memLp hw o (n+k)).const_mul (c n))
    have he : ((radial_mul_memLp hw o (n+k)).const_mul (c n)).toLp
        (fun x => c n*(w x*radialCutoff o (n+k) x)) =
        c n • (radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x) :=
      (radial_mul_memLp hw o (n+k)).toLp_const_smul (c n)
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hc n).1]
    exact inv_mul_cancel₀ (hpos n).ne'

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma normalized_radial_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => ((radial_mul_memLp hf o (n+k)).const_mul (c n)).toLp
      (fun x => c n*(f x*radialCutoff o (n+k) x))) atTop (𝓝 (hf.toLp f)) := by
  have H := hc.smul ((radial_mul_tendsto hf o).comp (tendsto_add_atTop_nat k))
  have he (n : ℕ) : ((radial_mul_memLp hf o (n+k)).const_mul (c n)).toLp
      (fun x => c n*(f x*radialCutoff o (n+k) x)) =
      c n • (radial_mul_memLp hf o (n+k)).toLp (fun x => f x*radialCutoff o (n+k) x) :=
    (radial_mul_memLp hf o (n+k)).toLp_const_smul (c n)
  simp_rw [he]
  simpa only [one_smul,Function.comp_apply] using H

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma normalized_radial_weighted_tendsto {w W : X → ℝ}
    (hW : MemLp (fun x => w x*W x) 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    ∃ hs : ∀ n, MemLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) 2 m,
      Tendsto (fun n => ‖(hs n).toLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x)‖)
        atTop (𝓝 0) := by
  have he (n : ℕ) : (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) =
      fun x => c n*(w x*W x*radialCutoff o (n+k) x)-w x*W x := by funext x; ring
  have hs (n : ℕ) : MemLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) 2 m := by
    rw [he]; exact ((radial_mul_memLp hW o (n+k)).const_mul (c n)).sub hW
  refine ⟨hs,?_⟩
  have heq (n : ℕ) : (hs n).toLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) =
      ((radial_mul_memLp hW o (n+k)).const_mul (c n)).toLp
        (fun x => c n*(w x*W x*radialCutoff o (n+k) x))-hW.toLp (fun x => w x*W x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    exact he n
  simp_rw [heq]
  simpa only [sub_self,norm_zero] using ((normalized_radial_tendsto hW o k hc).sub_const (hW.toLp _)).norm

lemma CurvatureDimension.normalized_radial_root_strong {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (hq : QuadraticCheegerEnergy m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hcn : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 1)) :
    ∃ hs : ∀ n, Sobolev m (fun x => c n*(w x*radialCutoff o (n+k) x)),
      Tendsto (fun n => ‖((hs n).sub hfin hw).2.2.toLp
        (weakGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)-w x))‖) atTop (𝓝 0) := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let fs (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hfs (n : ℕ) : MemLp (fs n) 2 m := (radial_mul_memLp hw.1 o (n+k)).const_mul (c n)
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEU (n : ℕ) : IsLocalWeakUpperGradient m (fs n) (Es n) := by
    simpa only [abs_of_nonneg (hcn n),fs,Es] using (hUG (n+k)).const_mul (c n)
  let hs (n : ℕ) := Sobolev.of_upperGradient hfin (hfs n) (hEU n) (hEs n)
  have hET : Tendsto (fun n => (hEs n).toLp (Es n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
    have H := hc.smul (hDT.comp (tendsto_add_atTop_nat k))
    have he (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) :=
      (hDs (n+k)).toLp_const_smul (c n)
    simp_rw [he]
    simpa only [Function.comp_apply,one_smul] using H
  obtain ⟨hsub,hST⟩ := hcd.strong_root_approximation hfin hq o hw fs Es hfs hEs hEU
    (normalized_radial_tendsto hw.1 o k hc) hET
  exact ⟨hs,hST⟩
end WeakHessian

end
end InlinedFile29

end OAI
