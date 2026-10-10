import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.StrongRoots
import OAI.Geometry.WeakHessian.Sobolev.SobolevPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile28
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_mul_memLp {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (n : ℕ) :
    MemLp (fun x => f x*radialCutoff o n x) 2 m :=
  memLp_mul_bounded hf (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_mul_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) :
    Tendsto (fun n => (radial_mul_memLp hf o n).toLp (fun x => f x*radialCutoff o n x))
      atTop (𝓝 (hf.toLp f)) := by
  apply toLp_tendsto_of_domination (fun n => radial_mul_memLp hf o n) hf hf
  · intro n
    apply ae_of_all
    intro x
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]
      exact radialCutoff_le_one o n x)
  · exact ae_of_all _ fun x => by simpa only [mul_one] using (radialCutoff_tendsto o x).const_mul (f x)

omit [ProperSpace X] in
lemma radial_root_approximation (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) :
    ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
      (∀ n, IsLocalWeakUpperGradient m (fun x => w x*radialCutoff o n x) (Ds n)) ∧
      Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
        (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  let D := weakGradient m w
  let c (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
  let Ds (n : ℕ) (x : X) := D x*radialCutoff o n x+c n*|w x|
  let hDs (n : ℕ) : MemLp (Ds n) 2 m := (radial_mul_memLp hw.2.2 o n).add (by
    simpa only [Real.norm_eq_abs] using hw.1.norm.const_mul (c n))
  refine ⟨Ds,hDs,?_,?_⟩
  · intro n
    have H := (weakGradient_isMinimal hw.2.1.2).1.mul_bounded
      (lipschitz_isLocalWeakUpperGradient hfin (radialCutoff_lipschitz o n)) hw.2.1.1
      (radialCutoff_lipschitz o n).continuous.measurable.aemeasurable
      (A := 1) (B := c n)
      (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
      (ae_of_all _ fun x => by simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; exact le_of_eq (abs_of_nonneg (by positivity)))
    simpa only [abs_of_nonneg (radialCutoff_nonneg o n _),NNReal.coe_inv,NNReal.coe_add,
      NNReal.coe_natCast,NNReal.coe_one,mul_comm,D,Ds,c] using H
  · have hc : Tendsto c atTop (𝓝 (0:ℝ)) := by
      simpa only [c,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hn : MemLp (fun x => |w x|) 2 m := by simpa only [Real.norm_eq_abs] using hw.1.norm
    have H := (radial_mul_tendsto hw.2.2 o).add (hc.smul (tendsto_const_nhds (x := hn.toLp (fun x => |w x|))))
    have he (n : ℕ) : (hDs n).toLp (Ds n) =
        (radial_mul_memLp hw.2.2 o n).toLp (fun x => D x*radialCutoff o n x)+c n • hn.toLp (fun x => |w x|) := by
      rw [← MemLp.toLp_const_smul,← MemLp.toLp_add]
      congr 1
    simp_rw [he]
    simpa only [zero_smul,add_zero] using H

lemma radial_root_strong {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (hq : QuadraticCheegerEnergy m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) :
    ∃ hs : ∀ n, Sobolev m (fun x => w x*radialCutoff o n x-w x),
      Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => w x*radialCutoff o n x-w x))‖)
        atTop (𝓝 0) := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  exact hcd.strong_root_approximation hfin hq o hw _ Ds (fun n => radial_mul_memLp hw.1 o n)
    hDs hUG (radial_mul_tendsto hw.1 o) hDT

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_weighted_root_tendsto {w W : X → ℝ} (hW : MemLp (fun x => w x*W x) 2 m) (o : X) :
    ∃ hs : ∀ n, MemLp (fun x => (w x*radialCutoff o n x-w x)*W x) 2 m,
      Tendsto (fun n => ‖(hs n).toLp (fun x => (w x*radialCutoff o n x-w x)*W x)‖)
        atTop (𝓝 0) := by
  have he (n : ℕ) : (fun x => (w x*radialCutoff o n x-w x)*W x) =
      fun x => w x*W x*radialCutoff o n x-w x*W x := by funext x; ring
  have hs (n : ℕ) : MemLp (fun x => (w x*radialCutoff o n x-w x)*W x) 2 m := by
    rw [he]; exact (radial_mul_memLp hW o n).sub hW
  refine ⟨hs,?_⟩
  have H := ((radial_mul_tendsto hW o).sub (tendsto_const_nhds (x := hW.toLp _))).norm
  have heq (n : ℕ) : (hs n).toLp (fun x => (w x*radialCutoff o n x-w x)*W x) =
      (radial_mul_memLp hW o n).toLp (fun x => w x*W x*radialCutoff o n x)-hW.toLp (fun x => w x*W x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    exact he n
  simp_rw [heq]
  simpa only [sub_self,norm_zero] using H
end WeakHessian

end
end InlinedFile28

end OAI
