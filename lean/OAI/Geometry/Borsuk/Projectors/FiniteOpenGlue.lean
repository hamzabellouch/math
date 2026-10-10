import Mathlib

namespace OAI

namespace BorsukNine
open scoped BigOperators Topology

noncomputable def finiteOpenGlue {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    (S : κ → Set X) (f : κ → X → Y) : X → Y :=
  by classical exact fun x => ∑ i, if x ∈ S i then f i x else 0

lemma finiteOpenGlue_eq {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    {S : κ → Set X} (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (f : κ → X → Y)
    {i : κ} {x : X} (hx : x ∈ S i) : finiteOpenGlue S f x = f i x := by
  classical
  rw [finiteOpenGlue,Finset.sum_eq_single i]
  · simp [hx]
  · intro j hj hji
    have hjx : x ∉ S j := fun hp => Set.disjoint_left.mp (hS hji) hp hx
    simp [hjx]
  · simp

lemma finiteOpenGlue_continuousOn {κ X Y : Type*} [Fintype κ]
    [TopologicalSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    {S : κ → Set X} (hSo : ∀ i, IsOpen (S i)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : κ → X → Y) (hf : ∀ i, ContinuousOn (f i) (S i)) :
    ContinuousOn (finiteOpenGlue S f) (⋃ i, S i) := by
  intro x hx
  obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
  have hn : ∀ᶠ y in 𝓝 x, y ∈ S i := (hSo i).mem_nhds hxi
  have hc := (hf i x hxi).continuousAt ((hSo i).mem_nhds hxi)
  apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [hn] with y hy
  exact finiteOpenGlue_eq hS f hy

lemma finiteOpenGlue_continuousOn_prod {κ X Y : Type*} [Fintype κ]
    [TopologicalSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    {S : κ → Set X} (hSo : ∀ i, IsOpen (S i)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : κ → ℝ × X → Y) (hf : ∀ i, ContinuousOn (f i) (Set.Icc (0:ℝ) 1 ×ˢ S i)) :
    ContinuousOn (finiteOpenGlue (fun i => {p : ℝ × X | p.2 ∈ S i}) f)
      (Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i) := by
  intro p hp
  obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp hp.2
  have hn : ∀ᶠ q in 𝓝 p, q.2 ∈ S i :=
    continuous_snd.continuousAt.preimage_mem_nhds ((hSo i).mem_nhds hpi)
  have hs : Set.Icc (0:ℝ) 1 ×ˢ S i ∈ 𝓝[Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i] p := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with q hq hqi
    exact ⟨hqi.1,hq⟩
  have hSp : Pairwise (fun i j => Disjoint {p : ℝ × X | p.2 ∈ S i} {p : ℝ × X | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => Set.disjoint_left.mp (hS hij) hi hj)
  apply ((hf i p ⟨hp.1,hpi⟩).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq
    exact finiteOpenGlue_eq hSp f hq
  · exact finiteOpenGlue_eq hSp f hpi

end BorsukNine

end OAI
