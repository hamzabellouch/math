import OAI.Analysis.CircleDomains.Topology.CompactBandNeighborhood
import OAI.Analysis.CircleDomains.Probability.CircleNullImage
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! The singleton band at a free point supplies a narrow branch
neighborhood. Second countability extracts the countable family used
in the local tag null-trace argument. -/

open Set MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem countable_narrow_real_band_cover
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    {D F W : Set X} {f a : X → ℝ} {M : ℝ}
    (hM : ∀ z ∈ D, |f z| ≤ M) (hW : IsOpen W) (hFW : F ⊆ W)
    (htrace : ∀ x ∈ F, ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a x) :
    ∃ (S : Set X) (V : X → Set X), S ⊆ F ∧ S.Countable ∧
      F ⊆ ⋃ x ∈ S, V x ∧ ∀ x ∈ S,
        IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ W ∧
        ∀ y ∈ V x, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
          t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
  have hn : ∀ x ∈ F, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x hx
    obtain ⟨V, hV, hxV, hv⟩ := exists_narrow_real_band_neighborhood hM (htrace x hx)
      (by norm_num : (0 : ℝ) < 1 / 4)
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hFW hx⟩, inter_subset_right, ?_⟩
    intro y hy t ht
    have hb := hv y hy.1 t ht
    constructor <;> linarith [hb.1, hb.2]
  have hchoice : ∀ x, ∃ V : Set X, x ∈ F → IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨V, hV⟩ := hn x hx
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => (hx h).elim⟩
  choose V hV using hchoice
  obtain ⟨S, hSF, hSc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := F) (f := V) (fun x hx => mem_nhdsWithin_of_mem_nhds ((hV x hx).1.mem_nhds (hV x hx).2.1))
  exact ⟨S, V, hSF, hSc, hcover, fun x hx => hV x (hSF hx)⟩

theorem circle_null_image_of_countable_local_traces
    {X I : Type*} [Countable I] (F : Set X) (w : X → UnitAddCircle)
    (V : I → Set X) (v : I → X → ℝ)
    (hcover : F ⊆ ⋃ i, V i)
    (hbranch : ∀ i x, x ∈ F ∩ V i → (v i x : UnitAddCircle) = w x)
    (hnull : ∀ i, volume (v i '' (F ∩ V i)) = 0) :
    volume (w '' F) = 0 := by
  have hs : w '' F ⊆ ⋃ i, ((↑) : ℝ → UnitAddCircle) '' (v i '' (F ∩ V i)) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, v i x, ⟨x, ⟨hx, hi⟩, rfl⟩, hbranch i x ⟨hx, hi⟩⟩
  exact measure_mono_null hs (measure_iUnion_null fun i => volume_addCircle_image_eq_zero (hnull i))

end CircleDomainRigidity

end

end OAI
