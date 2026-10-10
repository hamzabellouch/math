import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import OAI.Analysis.CircleDomains.Topology.CircleAlmostEverywhere
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Integrating the paid-threshold cover gives the local image payment.
The bands here are the actual compact real fibers. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

theorem interval_payment_of_ae_cover {I : Type*} [Countable I]
    (S : Set ℝ) (T : I → Set ℝ) (a b : ℝ)
    (hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      t ∈ S ∨ ∃ i, t ∈ T i) :
    ENNReal.ofReal (b - a) ≤ volume S + ∑' i, volume (T i) := by
  have hsub : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a b → t ∈ S ∪ ⋃ i, T i := by
    have h := (ae_restrict_iff' measurableSet_Ioo).mp hcover
    filter_upwards [h] with t ht htab
    rcases ht htab with hs | ⟨i, hi⟩
    · exact Or.inl hs
    · exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
  calc
    ENNReal.ofReal (b - a) = volume (Ioo a b) := (Real.volume_Ioo).symm
    _ ≤ volume (S ∪ ⋃ i, T i) := measure_mono_ae hsub
    _ ≤ volume S + volume (⋃ i, T i) := measure_union_le _ _
    _ ≤ volume S + ∑' i, volume (T i) := add_le_add le_rfl (measure_iUnion_le _)

theorem real_band_fiber_volume
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} (hx : x ∈ closure D) :
    volume {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph D f)} =
      ENNReal.ofReal (limsup f (𝓝[D] x) - liminf f (𝓝[D] x)) := by
  rw [intervalFiberHull_clusterGraph_eq_boundary_band hM hx, Real.volume_Icc]

theorem interval_band_payment_of_ae_cover
    {X I : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X] [Countable I]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    (s : I → X) (hs : ∀ i, s i ∈ closure D) (S : Set ℝ) (a b : ℝ)
    (hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      t ∈ S ∨ ∃ i, (s i, t) ∈ intervalFiberHull (clusterGraph D f)) :
    ENNReal.ofReal (b - a) ≤ volume S +
      ∑' i, ENNReal.ofReal (limsup f (𝓝[D] (s i)) - liminf f (𝓝[D] (s i))) := by
  have h := interval_payment_of_ae_cover S
    (fun i => {t | (s i, t) ∈ intervalFiberHull (clusterGraph D f)}) a b hcover
  simpa only [real_band_fiber_volume hM (hs _)] using h

end CircleDomainRigidity

end OAI
