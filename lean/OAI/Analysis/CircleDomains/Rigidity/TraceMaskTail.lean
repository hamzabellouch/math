import OAI.Analysis.CircleDomains.Rigidity.TraceMaskPrimitive

namespace OAI

/-! A tail which is inactive outside one scalar interval changes the
entire primitive by at most that interval's length. This is the local
finite approximation used at accumulating common-point components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem finiteTraceMask_tail_eq {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {N n : ℕ} (hn : N ≤ n)
    (htail : ∀ j, N ≤ j → t ∈ I j → cutoff j x = 1) :
    finiteTraceMask cutoff I x t n = finiteTraceMask cutoff I x t N := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [finiteTraceMask,ih]
    have he : (if t ∈ I n then cutoff n x else 1) = 1 := by
      split_ifs with ht
      · exact htail n hn ht
      · rfl
    rw [he,min_eq_left (finiteTraceMask_bounds hc I x t N).2]

 theorem infiniteTraceMask_tail_eq {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {N : ℕ}
    (htail : ∀ j, N ≤ j → t ∈ I j → cutoff j x = 1) :
    infiniteTraceMask cutoff I x t = finiteTraceMask cutoff I x t N := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (finiteTraceMask_tail_eq hc hn htail).symm

 theorem infiniteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (x : X) :
    Measurable (infiniteTraceMask cutoff I x) :=
  Measurable.iInf (fun n => finiteTraceMask_measurable cutoff hI x n)

 theorem infiniteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a b : ℝ) :
    IntervalIntegrable (infiniteTraceMask cutoff I x) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((infiniteTraceMask_measurable cutoff hI x).aestronglyMeasurable.restrict)
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs,abs_of_nonneg (infiniteTraceMask_bounds hc I x s).1]
  exact (infiniteTraceMask_bounds hc I x s).2

 theorem tracePrimitive_tail_bound {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJf : volume J ≠ ∞) {x : X} {N : ℕ}
    (htail : ∀ j, N ≤ j → ∀ t ∈ I j, t ∉ J → cutoff j x = 1)
    (a t : ℝ) :
    |infiniteTracePrimitive cutoff I a x t-finiteTracePrimitive cutoff I a x t N| ≤
      volume.real J := by
  let p := J.indicator (fun _ => (1 : ℝ))
  have hp : Integrable p volume := (integrableOn_const hJf).integrable_indicator hJ
  have hp0 (s : ℝ) : 0 ≤ p s := indicator_nonneg (fun _ _ => zero_le_one) s
  have hbound (s : ℝ) :
      ‖infiniteTraceMask cutoff I x s-finiteTraceMask cutoff I x s N‖ ≤ p s := by
    by_cases hs : s ∈ J
    · rw [show p s = 1 from indicator_of_mem hs _]
      rw [Real.norm_eq_abs,abs_le]
      have h1 := infiniteTraceMask_bounds hc I x s
      have h2 := finiteTraceMask_bounds hc I x s N
      constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
    · rw [infiniteTraceMask_tail_eq hc (fun j hj hij => htail j hj s hij hs),sub_self,norm_zero]
      exact hp0 s
  rw [infiniteTracePrimitive,finiteTracePrimitive,← intervalIntegral.integral_sub
    (infiniteTraceMask_intervalIntegrable hc hI x a t)
    (finiteTraceMask_intervalIntegrable hc hI x N a t),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s in uIoc a t, ‖infiniteTraceMask cutoff I x s-finiteTraceMask cutoff I x s N‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in uIoc a t, p s := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => norm_nonneg _)) hp.restrict
      (Eventually.of_forall hbound)
    _ ≤ ∫ s, p s := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hp0) hp
    _ = volume.real J := integral_indicator_one hJ

end CircleDomainRigidity

end

end OAI
