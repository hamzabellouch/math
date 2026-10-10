import OAI.Analysis.CircleDomains.Rigidity.TracePrimitiveContinuity

namespace OAI

/-! On an indexed component neighborhood an active zero cutoff fixes the
upper endpoint of the primitive. Late intervals absorbed by that same
zero interval have no effect, so the infinite masked scalar is locally
an actual finite continuous primitive, even when the raw scalar jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j : ℕ} (ht : t ∈ I j) (hz : cutoff j x = 0) :
    infiniteTraceMask cutoff I x t = 0 := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  exact (finiteTraceMask_zero_of_active hc hn ht hz).symm

 theorem infiniteTracePrimitive_plateau {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {x : X} {j : ℕ}
    (hconv : OrdConnected (I j)) (hz : cutoff j x = 0) {s t : ℝ}
    (hs : s ∈ I j) (ht : t ∈ I j) (a : ℝ) :
    infiniteTracePrimitive cutoff I a x s = infiniteTracePrimitive cutoff I a x t := by
  apply sub_eq_zero.mp
  rw [infiniteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.integral_interval_sub_left
      (infiniteTraceMask_intervalIntegrable hc hI x a s)
      (infiniteTraceMask_intervalIntegrable hc hI x a t)]
  calc
    _ = ∫ u in t..s, (0 : ℝ) := intervalIntegral.integral_congr (fun u hu =>
      infiniteTraceMask_zero_of_active hc (hconv.uIcc_subset ht hs hu) hz)
    _ = 0 := by simp

 theorem infiniteTraceMask_absorbed_tail {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {j N : ℕ} (hj : j < N) (hz : cutoff j x = 0)
    (htail : ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k x ≠ 1 → t ∈ I j) (t : ℝ) :
    infiniteTraceMask cutoff I x t = finiteTraceMask cutoff I x t N := by
  by_cases ht : t ∈ I j
  · rw [infiniteTraceMask_zero_of_active hc ht hz,finiteTraceMask_zero_of_active hc hj ht hz]
  · apply infiniteTraceMask_tail_eq hc
    intro k hk hkI
    by_contra he
    exact ht (htail k hk t hkI he)

 theorem infiniteTracePrimitive_absorbed_tail {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {j N : ℕ} (hj : j < N) (hz : cutoff j x = 0)
    (htail : ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k x ≠ 1 → t ∈ I j) (a t : ℝ) :
    infiniteTracePrimitive cutoff I a x t = finiteTracePrimitive cutoff I a x t N := by
  apply intervalIntegral.integral_congr
  intro u _
  exact infiniteTraceMask_absorbed_tail hc hj hz htail u

 theorem indexed_masked_scalar_continuousAt {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} {x : X} {j N : ℕ} (hj : j < N)
    (hconv : OrdConnected (I j)) {β : ℝ} (hβ : β ∈ I j) (a : ℝ)
    (hnear : ∀ᶠ y in 𝓝 x, cutoff j y = 0 ∧ b y ∈ I j ∧
      ∀ k, N ≤ k → ∀ t ∈ I k, cutoff k y ≠ 1 → t ∈ I j) :
    ContinuousAt (fun y => infiniteTracePrimitive cutoff I a y (b y)) x := by
  have hh : (fun y => infiniteTracePrimitive cutoff I a y (b y)) =ᶠ[𝓝 x]
      (fun y => finiteTracePrimitive cutoff I a y β N) := by
    filter_upwards [hnear] with y hy
    rw [infiniteTracePrimitive_plateau hc hI hconv hy.1 hy.2.1 hβ a,
      infiniteTracePrimitive_absorbed_tail hc hj hy.1 hy.2.2 a β]
  have hcont : ContinuousAt (fun y => finiteTracePrimitive cutoff I a y β N) x :=
    (finiteTracePrimitive_continuous hc hcc hI hIf a N).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  exact hcont.congr_of_eventuallyEq hh

end CircleDomainRigidity

end

end OAI
