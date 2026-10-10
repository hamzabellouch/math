import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Gluing, homotopy, and operations on vector bundle sections. -/

section
open Bundle Topology
namespace Kaplansky

section
variable {B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace V E)]
  [FiberBundle V E] [VectorBundle ℂ V E]

/-- Addition over a varying base, with the actual total-space topology. -/
theorem continuous_bundle_add_over {X : Type*} [TopologicalSpace X]
    (b : X → B) (hb : Continuous b) (v w : ∀ x, E (b x))
    (hv : Continuous (fun x => TotalSpace.mk' V (b x) (v x)))
    (hw : Continuous (fun x => TotalSpace.mk' V (b x) (w x))) :
    Continuous (fun x => TotalSpace.mk' V (b x) (v x + w x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  have hv' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hv.continuousAt |>.2
  have hw' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hw.continuousAt |>.2
  apply (hv'.add hw').congr_of_eventuallyEq
  let e := trivializationAt V E (b x)
  have hn := hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (b x)))
  filter_upwards [hn] with y hy
  exact (e.linear ℂ hy).map_add (v y) (w y)

/-- Scalar multiplication over a varying base. -/
theorem continuous_bundle_smul_over {X : Type*} [TopologicalSpace X]
    (b : X → B) (hb : Continuous b) (c : X → ℂ) (hc : Continuous c)
    (v : ∀ x, E (b x))
    (hv : Continuous (fun x => TotalSpace.mk' V (b x) (v x))) :
    Continuous (fun x => TotalSpace.mk' V (b x) (c x • v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  have hv' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hv.continuousAt |>.2
  apply (hc.continuousAt.smul hv').congr_of_eventuallyEq
  let e := trivializationAt V E (b x)
  have hn := hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (b x)))
  filter_upwards [hn] with y hy
  exact (e.linear ℂ hy).map_smul (c y) (v y)

/-- The genuine global affine homotopy of two continuous bundle sections.
It permits intermediate degenerate zeros. -/
def bundleSectionHomotopy (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) :
    ContinuousMap.Homotopy ⟨_, hs⟩ ⟨_, ht⟩ where
  toFun z := ⟨z.2, (1 - (z.1.val : ℂ)) • s z.2 + (z.1.val : ℂ) • t z.2⟩
  continuous_toFun := by
    apply continuous_bundle_add_over Prod.snd continuous_snd
    · apply continuous_bundle_smul_over Prod.snd continuous_snd
      · exact continuous_const.sub (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst))
      · exact hs.comp continuous_snd
    · apply continuous_bundle_smul_over Prod.snd continuous_snd
      · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      · exact ht.comp continuous_snd
  map_zero_left b := by simp
  map_one_left b := by simp

/-- The map of a section into the one-point compactification of its actual total space. -/
def compactifiedSection (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) :
    C(B, OnePoint (TotalSpace V E)) :=
  ⟨fun b => (TotalSpace.mk' V b (s b) : OnePoint (TotalSpace V E)),
    OnePoint.continuous_coe.comp hs⟩

/-- Global section independence at the level of homotopy, without a
regularity or finiteness assumption on any intermediate zero set. -/
def compactifiedSectionHomotopy (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) :
    ContinuousMap.Homotopy (compactifiedSection s hs) (compactifiedSection t ht) :=
  (ContinuousMap.Homotopy.refl ⟨_, OnePoint.continuous_coe⟩).comp
    (bundleSectionHomotopy s t hs ht)

end

variable {𝕜 Y F I : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Gluing compatible local coordinate functions produces a continuous
section of the ordinary, potentially nontrivial vector bundle. -/
theorem glue_core_section (H : VectorBundleCore 𝕜 Y F I)
    (L : I → Y → F) (hL : ∀ a, ContinuousOn (L a) (H.baseSet a))
    (hcompat : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      H.coordChange a b y (L a y) = L b y) :
    ∃ s : ∀ y, H.Fiber y,
      Continuous (fun y => TotalSpace.mk' F y (s y)) ∧
      ∀ a y, y ∈ H.baseSet a → (H.localTriv a ⟨y,s y⟩).2 = L a y := by
  let s : ∀ y, H.Fiber y := fun y => L (H.indexAt y) y
  have he (a : I) (y : Y) (hy : y ∈ H.baseSet a) :
      (H.localTriv a ⟨y,s y⟩).2 = L a y :=
    hcompat (H.indexAt y) a y (H.mem_baseSet_at y) hy
  refine ⟨s, ?_, he⟩
  rw [continuous_iff_continuousAt]
  intro y
  rw [FiberBundle.continuousAt_section]
  have hn := (H.isOpen_baseSet (H.indexAt y)).mem_nhds (H.mem_baseSet_at y)
  have hc := (hL (H.indexAt y) y (H.mem_baseSet_at y)).continuousAt hn
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact he (H.indexAt y) z hz

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {𝕜 Y V : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
variable [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace V E)]
variable [FiberBundle V E] [VectorBundle 𝕜 V E]

include 𝕜 in
/-- Finite sums of continuous local sections in an ordinary vector bundle. -/
theorem continuousOn_bundle_sum {ι : Type*} (u : Finset ι) (v : ι → ∀ y, E y) {s : Set Y}
    (hv : ∀ i ∈ u, ContinuousOn (fun y => TotalSpace.mk' V y (v i y)) s) :
    ContinuousOn (fun y => TotalSpace.mk' V y (∑ i ∈ u, v i y)) s := by
  intro y hy
  rw [FiberBundle.continuousWithinAt_section]
  have hc : ContinuousWithinAt
      (fun z => ∑ i ∈ u, ((trivializationAt V E y) ⟨z,v i z⟩).2) s y :=
    tendsto_finsetSum u (fun i hi =>
    ((FiberBundle.continuousWithinAt_section V).mp (hv i hi y hy)))
  apply hc.congr_of_eventuallyEq
  ·
    have hn := (trivializationAt V E y).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E y)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with z hz
    exact (map_sum (((trivializationAt V E y).linear 𝕜 hz).mk' _) (fun i => v i z) u)
  · exact map_sum (((trivializationAt V E y).linear 𝕜 (mem_baseSet_trivializationAt V E y)).mk' _) (fun i => v i y) u

/-- Scalar multiplication of continuous local sections. -/
theorem continuousOn_bundle_smul (f : Y → 𝕜) (v : ∀ y, E y) {s : Set Y}
    (hf : ContinuousOn f s) (hv : ContinuousOn (fun y => TotalSpace.mk' V y (v y)) s) :
    ContinuousOn (fun y => TotalSpace.mk' V y (f y • v y)) s := by
  intro y hy
  rw [FiberBundle.continuousWithinAt_section]
  have hc := (hf y hy).smul ((FiberBundle.continuousWithinAt_section V).mp (hv y hy))
  apply hc.congr_of_eventuallyEq
  ·
    have hn := (trivializationAt V E y).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E y)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with z hz
    exact (((trivializationAt V E y).linear 𝕜 hz).map_smul (f z) (v z))
  · exact ((trivializationAt V E y).linear 𝕜 (mem_baseSet_trivializationAt V E y)).map_smul (f y) (v y)

end Kaplansky

end

end OAI
