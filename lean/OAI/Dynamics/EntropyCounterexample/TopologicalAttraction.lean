import Mathlib

namespace OAI

noncomputable section
open Filter Set Metric
open scoped Topology

namespace Problem340.TopologicalAttraction

variable {ι X Y Z W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem tendsto_fst_fiber [CompactSpace Y] {l : Filter ι}
    {x : ι → X} (y : ι → Y) {a : X} (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => (x i, y i)) l (𝓝ˢ {p : X × Y | p.1 = a}) := by
  have hy : Tendsto y l (𝓝ˢ (univ : Set Y)) := by simp [nhdsSet_univ]
  have ht : Tendsto (fun i => (x i, y i)) l (𝓝ˢ ({a} ×ˢ (univ : Set Y))) := by
    rw [isCompact_singleton.nhdsSet_prod_eq isCompact_univ, nhdsSet_singleton]
    exact hx.prodMk hy
  convert ht using 1
  congr 1
  ext p
  simp

theorem tendsto_snd_fiber [CompactSpace X] {l : Filter ι}
    (x : ι → X) {y : ι → Y} {b : Y} (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => (x i, y i)) l (𝓝ˢ {p : X × Y | p.2 = b}) := by
  have hx : Tendsto x l (𝓝ˢ (univ : Set X)) := by simp [nhdsSet_univ]
  have ht : Tendsto (fun i => (x i, y i)) l (𝓝ˢ ((univ : Set X) ×ˢ {b})) := by
    rw [isCompact_univ.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton]
    exact hx.prodMk hy
  convert ht using 1
  congr 1
  ext p
  simp

theorem tendsto_fixed_clock_main [CompactSpace Z] {l : Filter ι}
    {x : ι → X} {y : ι → Y} (z : ι → Z) {a : X} {b : Y}
    (hx : Tendsto x l (𝓝 a)) (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b}) := by
  have hz : Tendsto z l (𝓝ˢ (univ : Set Z)) := by simp [nhdsSet_univ]
  have hyz : Tendsto (fun i => (y i, z i)) l (𝓝ˢ ({b} ×ˢ (univ : Set Z))) := by
    rw [isCompact_singleton.nhdsSet_prod_eq isCompact_univ, nhdsSet_singleton]
    exact hy.prodMk hz
  have ht : Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ ({a} ×ˢ ({b} ×ˢ (univ : Set Z)))) := by
    rw [isCompact_singleton.nhdsSet_prod_eq (isCompact_singleton.prod isCompact_univ),
      nhdsSet_singleton]
    exact hx.prodMk hyz
  convert ht using 1
  congr 1
  ext p
  simp

theorem tendsto_fixed_main_registers [CompactSpace X] {l : Filter ι}
    (x : ι → X) {y : ι → Y} {z : ι → Z} {b : Y} {c : Z}
    (hy : Tendsto y l (𝓝 b)) (hz : Tendsto z l (𝓝 c)) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ {p : X × (Y × Z) | p.2 = (b, c)}) :=
  tendsto_snd_fiber x (hy.prodMk_nhds hz)

theorem tendsto_two_attractors [CompactSpace X] [CompactSpace Z] {l : Filter ι}
    {x : ι → X} {y : ι → Y} {z : ι → Z} {a : X} {b₀ bInf : Y} {c : Z}
    (h : (Tendsto x l (𝓝 a) ∧ Tendsto y l (𝓝 b₀)) ∨
      (Tendsto y l (𝓝 bInf) ∧ Tendsto z l (𝓝 c))) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ ({p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} ∪
       {p : X × (Y × Z) | p.2 = (bInf, c)})) := by
  rcases h with ⟨hx, hy⟩ | ⟨hy, hz⟩
  · exact (tendsto_fixed_clock_main z hx hy).mono_right (nhdsSet_mono subset_union_left)
  · exact (tendsto_fixed_main_registers x hy hz).mono_right (nhdsSet_mono subset_union_right)

theorem tendsto_image [TopologicalSpace W] {l : Filter ι} {u : ι → X}
    {s : Set X} {p : X → W} (hp : Continuous p) (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => p (u i)) l (𝓝ˢ (p '' s)) :=
  (hp.tendsto_nhdsSet (mapsTo_image p s)).comp h

theorem tendsto_infDist [PseudoMetricSpace W] {l : Filter ι} {u : ι → W}
    {s : Set W} (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => infDist (u i) s) l (𝓝 0) := by
  exact ((continuous_infDist_pt s).tendsto_nhdsSet_nhds
    (fun _ hs => infDist_zero_of_mem hs)).comp h

theorem tendsto_infDist_image [PseudoMetricSpace W] {l : Filter ι} {u : ι → X}
    {s : Set X} {p : X → W} (hp : Continuous p) (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => infDist (p (u i)) (p '' s)) l (𝓝 0) :=
  tendsto_infDist (tendsto_image hp h)

end Problem340.TopologicalAttraction

end

end OAI
