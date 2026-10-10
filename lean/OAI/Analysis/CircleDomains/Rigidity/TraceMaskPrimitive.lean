import OAI.Analysis.CircleDomains.Rigidity.FiniteTraceMask
import OAI.Analysis.CircleDomains.Rigidity.TraceCompression
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Integral primitives of the actual finite and infinite trace masks.
The finite spatial variation is bounded by interval lengths times cutoff
variation, while endpoint changes are always one-Lipschitz. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def finiteTracePrimitive {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (a : ℝ) (x : X) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in a..t, finiteTraceMask cutoff I x s n

 def infiniteTracePrimitive {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (a : ℝ) (x : X) (t : ℝ) : ℝ :=
  ∫ s in a..t, infiniteTraceMask cutoff I x s

 theorem finiteTraceMask_norm_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) (n : ℕ) :
    ‖finiteTraceMask cutoff I x s n‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteTraceMask_bounds hc I x s n).1]
  exact (finiteTraceMask_bounds hc I x s n).2

 theorem finiteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => finiteTraceMask cutoff I x s n) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
    (Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))

 theorem finiteTracePrimitive_sub {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a s t : ℝ) :
    finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a x s n =
      ∫ u in s..t, finiteTraceMask cutoff I x u n :=
  intervalIntegral.integral_interval_sub_left
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI x n a s)

 theorem finiteTracePrimitive_lipschitz {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a : ℝ) :
    LipschitzWith 1 (fun t => finiteTracePrimitive cutoff I a x t n) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [Real.dist_eq,Real.dist_eq,← Real.norm_eq_abs,finiteTracePrimitive_sub hc hI]
  simpa only [NNReal.coe_one,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := s) (b := t)
      (fun u _ => finiteTraceMask_norm_le hc I x u n)

 theorem finiteTracePrimitive_variation {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (x y : X) (a t : ℝ) (n : ℕ) :
    |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
      ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j x-cutoff j y| := by
  let p := fun s => ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) s
  have hi (j : ℕ) : Integrable ((I j).indicator (fun _ => |cutoff j x-cutoff j y|)) volume :=
    (integrableOn_const (hIf j)).integrable_indicator (hI j)
  have hp : Integrable p volume := integrable_finsetSum _ (fun j _ => hi j)
  have hp0 (s : ℝ) : 0 ≤ p s :=
    Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) s)
  rw [finiteTracePrimitive,finiteTracePrimitive,← intervalIntegral.integral_sub
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI y n a t),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s in uIoc a t, ‖finiteTraceMask cutoff I x s n-finiteTraceMask cutoff I y s n‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in uIoc a t, p s := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => norm_nonneg _)) hp.restrict
      (Eventually.of_forall (fun s => by
        simpa only [Real.norm_eq_abs] using finiteTraceMask_variation cutoff I x y s n))
    _ ≤ ∫ s, p s := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hp0) hp
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => hi j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_indicator_const _ (hI j)

 theorem infiniteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) :
    infiniteTraceMask cutoff I x s ∈ Icc (0:ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (finiteTraceMask_tendsto hc I x s)
    (Eventually.of_forall (fun n => finiteTraceMask_bounds hc I x s n))

 theorem finiteTracePrimitive_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a t : ℝ) :
    Tendsto (fun n => finiteTracePrimitive cutoff I a x t n) atTop
      (𝓝 (infiniteTracePrimitive cutoff I a x t)) := by
  have ht : Tendsto (fun n => ∫ s in uIoc a t, finiteTraceMask cutoff I x s n) atTop
      (𝓝 (∫ s in uIoc a t, infiniteTraceMask cutoff I x s)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a t).def'
      (fun n => Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))
      (Eventually.of_forall (fun s => finiteTraceMask_tendsto hc I x s))
  simpa only [finiteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    ht.const_smul (if a ≤ t then (1 : ℝ) else -1)

end CircleDomainRigidity

end

end OAI
