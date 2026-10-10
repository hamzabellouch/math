import OAI.Analysis.CircleDomains.Rigidity.TraceMaskLinePayment
import OAI.Analysis.CircleDomains.Rigidity.TraceIntervalPayment

namespace OAI

/-! An inactive prefix lets scalar tail compression be compared with the
actual infinite mask. The spatial payment is valid across all component
types; continuity of the unmasked scalar is not required. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTraceMask_eq_one {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ} {x : X} {t : ℝ}
    (h : ∀ j, t ∈ I j → cutoff j x = 1) : infiniteTraceMask cutoff I x t = 1 := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  exact tendsto_const_nhds.congr' (Eventually.of_forall (fun n =>
    (finiteTraceMask_eq_one (fun j _ => h j)).symm))

 theorem traceCompression_increment_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {E : Set ℝ} (hE : MeasurableSet E)
    (x : X) (hactive : ∀ j t, t ∈ I j → t ∉ E → cutoff j x = 1)
    (a : ℝ) {s t : ℝ} (hst : s ≤ t) :
    traceCompression E a t-traceCompression E a s ≤
      infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a x s := by
  rw [traceCompression_sub hE]
  rw [infiniteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.integral_interval_sub_left
      (infiniteTraceMask_intervalIntegrable hc hI x a t)
      (infiniteTraceMask_intervalIntegrable hc hI x a s)]
  apply intervalIntegral.integral_mono_on hst
    (traceCompression_intervalIntegrable hE s t)
    (infiniteTraceMask_intervalIntegrable hc hI x s t)
  intro u _
  by_cases hu : u ∈ E
  · rw [indicator_of_notMem (show u ∉ Eᶜ from fun h => h hu) _]
    exact (infiniteTraceMask_bounds hc I x u).1
  · rw [indicator_of_mem hu _,infiniteTraceMask_eq_one hc (fun j hj => hactive j u hj hu)]

 theorem masked_trace_compression_payment {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {E : Set ℝ} (hE : MeasurableSet E)
    {V : Set X} (hactive : ∀ z ∈ V, ∀ j t, t ∈ I j → t ∉ E → cutoff j z = 1)
    (a : ℝ) (b : X → ℝ) {x y : X} (hx : x ∈ V) (hy : y ∈ V) {p : ℝ}
    (hpay : ∀ t, |infiniteTracePrimitive cutoff I a x t-
      infiniteTracePrimitive cutoff I a y t| ≤ p) :
    |traceCompression E a (b x)-traceCompression E a (b y)| ≤
      |infiniteTracePrimitive cutoff I a x (b x)-
        infiniteTracePrimitive cutoff I a y (b y)|+p := by
  let F : V → ℝ → ℝ := fun z => infiniteTracePrimitive cutoff I a z.val
  let B : V → ℝ := fun z => b z.val
  exact compression_comparison F B (traceCompression E a) (traceCompression_monotone hE a)
    (fun z _ _ hst => traceCompression_increment_le hc hI hE z.val
      (hactive z z.property) a hst) (x := ⟨x,hx⟩) (y := ⟨y,hy⟩) hpay

end CircleDomainRigidity

end

end OAI
