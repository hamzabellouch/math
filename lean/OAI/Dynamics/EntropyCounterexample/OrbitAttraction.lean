import Mathlib

namespace OAI

noncomputable section
open Filter Metric
open scoped Topology

namespace Problem340.OrbitAttraction

variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem tendsto_infDist_of_approximation {l : Filter ι} {x y : ι → X} {s : Set X}
    (hy : ∀ i, y i ∈ s) (h : Tendsto (fun i => dist (x i) (y i)) l (𝓝 0)) :
    Tendsto (fun i => infDist (x i) s) l (𝓝 0) := by
  exact squeeze_zero (fun _ => infDist_nonneg)
    (fun i => infDist_le_dist_of_mem (hy i)) h

theorem infDist_fst_fiber (x : X) (y : Y) (a : X) :
    infDist (x, y) {p : X × Y | p.1 = a} = dist x a := by
  apply le_antisymm
  · simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist x a)]
      using (infDist_le_dist_of_mem (x := (x, y))
        (y := (a, y)) (s := {p : X × Y | p.1 = a}) rfl)
  · apply (le_infDist (s := {p : X × Y | p.1 = a}) ⟨(a, y), rfl⟩).2
    rintro ⟨u, v⟩ hu
    change u = a at hu
    simp only [Prod.dist_eq, hu]
    exact le_max_left _ _

theorem infDist_snd_fiber (x : X) (y : Y) (b : Y) :
    infDist (x, y) {p : X × Y | p.2 = b} = dist y b := by
  apply le_antisymm
  · simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist y b)]
      using (infDist_le_dist_of_mem (x := (x, y))
        (y := (x, b)) (s := {p : X × Y | p.2 = b}) rfl)
  · apply (le_infDist (s := {p : X × Y | p.2 = b}) ⟨(x, b), rfl⟩).2
    rintro ⟨u, v⟩ hv
    change v = b at hv
    simp only [Prod.dist_eq, hv]
    exact le_max_right _ _

theorem tendsto_infDist_fst_fiber {l : Filter ι} {x : ι → X} (y : ι → Y) {a : X}
    (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => infDist (x i, y i) {p : X × Y | p.1 = a}) l (𝓝 0) := by
  simp_rw [infDist_fst_fiber]
  exact tendsto_iff_dist_tendsto_zero.mp hx

theorem tendsto_infDist_snd_fiber {l : Filter ι} (x : ι → X) {y : ι → Y} {b : Y}
    (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => infDist (x i, y i) {p : X × Y | p.2 = b}) l (𝓝 0) := by
  simp_rw [infDist_snd_fiber]
  exact tendsto_iff_dist_tendsto_zero.mp hy

theorem tendsto_infDist_of_subset {l : Filter ι} {x : ι → X} {s t : Set X}
    (hs : s.Nonempty) (hst : s ⊆ t)
    (h : Tendsto (fun i => infDist (x i) s) l (𝓝 0)) :
    Tendsto (fun i => infDist (x i) t) l (𝓝 0) := by
  exact squeeze_zero (fun _ => infDist_nonneg)
    (fun _ => infDist_le_infDist_of_subset hst hs) h

theorem tendsto_infDist_union {l : Filter ι} {x : ι → X} {s t : Set X}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (h : Tendsto (fun i => infDist (x i) s) l (𝓝 0) ∨
      Tendsto (fun i => infDist (x i) t) l (𝓝 0)) :
    Tendsto (fun i => infDist (x i) (s ∪ t)) l (𝓝 0) := by
  rcases h with h | h
  · exact tendsto_infDist_of_subset hs Set.subset_union_left h
  · exact tendsto_infDist_of_subset ht Set.subset_union_right h

theorem tendsto_infDist_image {l : Filter ι} {x : ι → X} {s : Set X} {f : X → Y}
    (hs : s.Nonempty) (hf : UniformContinuous f)
    (h : Tendsto (fun i => infDist (x i) s) l (𝓝 0)) :
    Tendsto (fun i => infDist (f (x i)) (f '' s)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfd⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  filter_upwards [h δ hδ] with i hi
  have hi' : infDist (x i) s < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] using hi
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hs).mp hi'
  have hb : infDist (f (x i)) (f '' s) < ε :=
    (infDist_le_dist_of_mem (x := f (x i)) (s := f '' s)
      (y := f y) ⟨y, hy, rfl⟩).trans_lt (hfd hxy)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] using hb

theorem tendsto_infDist_image_of_compact [CompactSpace X]
    {l : Filter ι} {x : ι → X} {s : Set X} {f : X → Y}
    (hs : s.Nonempty) (hf : Continuous f)
    (h : Tendsto (fun i => infDist (x i) s) l (𝓝 0)) :
    Tendsto (fun i => infDist (f (x i)) (f '' s)) l (𝓝 0) :=
  tendsto_infDist_image hs (CompactSpace.uniformContinuous_of_continuous hf) h

theorem tendsto_nhdsSet_of_infDist {l : Filter ι} {x : ι → X} {s : Set X}
    (hc : IsCompact s) (hs : s.Nonempty)
    (h : Tendsto (fun i => infDist (x i) s) l (𝓝 0)) :
    Tendsto x l (𝓝ˢ s) := by
  apply (Metric.tendsto_nhdsSet hc hs).2
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp h ε hε] with i hi
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] using hi

theorem tendsto_infDist_semiconjugate [CompactSpace X]
    {f : X → X} {g : Y → Y} {p : X → Y} {s : Set X} {x : X}
    (hs : s.Nonempty) (hp : Continuous p) (hpg : Function.Semiconj p f g)
    (h : Tendsto (fun n : ℕ => infDist (f^[n] x) s) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => infDist (g^[n] (p x)) (p '' s)) atTop (𝓝 0) := by
  have ht := tendsto_infDist_image_of_compact hs hp h
  simpa only [hpg.iterate_right _ _] using ht

section ThreeFactors
variable {Z : Type*} [PseudoMetricSpace Z]

theorem tendsto_infDist_fixed_clock_main {l : Filter ι}
    {x : ι → X} {y : ι → Y} (z : ι → Z) {a : X} {b : Y}
    (hx : Tendsto x l (𝓝 a)) (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => infDist (x i, (y i, z i))
      {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b}) l (𝓝 0) := by
  apply tendsto_infDist_of_approximation
    (s := {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b})
    (y := fun i => (a, (b, z i))) (fun _ => ⟨rfl, rfl⟩)
  have ht := (tendsto_iff_dist_tendsto_zero.mp hx).max
    (tendsto_iff_dist_tendsto_zero.mp hy)
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, max_self] using ht

theorem tendsto_infDist_fixed_main_registers {l : Filter ι}
    (x : ι → X) {y : ι → Y} {z : ι → Z} {b : Y} {c : Z}
    (hy : Tendsto y l (𝓝 b)) (hz : Tendsto z l (𝓝 c)) :
    Tendsto (fun i => infDist (x i, (y i, z i))
      {p : X × (Y × Z) | p.2 = (b, c)}) l (𝓝 0) :=
  tendsto_infDist_snd_fiber x (hy.prodMk_nhds hz)

theorem tendsto_infDist_two_attractors {l : Filter ι}
    {x : ι → X} {y : ι → Y} {z : ι → Z} {a : X} {b₀ bInf : Y} {c : Z}
    (h : (Tendsto x l (𝓝 a) ∧ Tendsto y l (𝓝 b₀)) ∨
      (Tendsto y l (𝓝 bInf) ∧ Tendsto z l (𝓝 c))) :
    Tendsto (fun i => infDist (x i, (y i, z i))
      ({p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} ∪
       {p : X × (Y × Z) | p.2 = (bInf, c)})) l (𝓝 0) := by
  have hs : Set.Nonempty {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} :=
    ⟨(a, (b₀, c)), rfl, rfl⟩
  have ht : Set.Nonempty {p : X × (Y × Z) | p.2 = (bInf, c)} :=
    ⟨(a, (bInf, c)), rfl⟩
  apply tendsto_infDist_union hs ht
  rcases h with ⟨hx, hy⟩ | ⟨hy, hz⟩
  · exact Or.inl (tendsto_infDist_fixed_clock_main z hx hy)
  · exact Or.inr (tendsto_infDist_fixed_main_registers x hy hz)

theorem isCompact_fixed_clock_main [CompactSpace Z] (a : X) (b : Y) :
    IsCompact {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b} := by
  have heq : {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b} =
      Set.range (fun z : Z => (a, (b, z))) := by
    ext p
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨p.2.2, Prod.ext ha.symm (Prod.ext hb.symm rfl)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨rfl, rfl⟩
  rw [heq]
  exact isCompact_range (continuous_const.prodMk (continuous_const.prodMk continuous_id))

theorem isCompact_fixed_main_registers [CompactSpace X] (b : Y) (c : Z) :
    IsCompact {p : X × (Y × Z) | p.2 = (b, c)} := by
  have heq : {p : X × (Y × Z) | p.2 = (b, c)} =
      Set.range (fun x : X => (x, (b, c))) := by
    ext p
    constructor
    · intro h
      exact ⟨p.1, Prod.ext rfl h.symm⟩
    · rintro ⟨x, rfl⟩
      rfl
  rw [heq]
  exact isCompact_range (continuous_id.prodMk continuous_const)

theorem isCompact_two_attractors [CompactSpace X] [CompactSpace Z]
    (a : X) (b₀ bInf : Y) (c : Z) :
    IsCompact ({p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} ∪
      {p : X × (Y × Z) | p.2 = (bInf, c)}) :=
  (isCompact_fixed_clock_main a b₀).union (isCompact_fixed_main_registers bInf c)

theorem tendsto_infDist_two_attractors_of_eventual_registers {l : Filter ι}
    {x : ι → X} {y : ι → Y} {z : ι → Z} {a : X} {b₀ bInf : Y} {c : Z}
    (h : (Tendsto x l (𝓝 a) ∧ Tendsto y l (𝓝 b₀)) ∨
      (Tendsto y l (𝓝 bInf) ∧ ∀ᶠ i in l, z i = c)) :
    Tendsto (fun i => infDist (x i, (y i, z i))
      ({p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} ∪
       {p : X × (Y × Z) | p.2 = (bInf, c)})) l (𝓝 0) := by
  apply tendsto_infDist_two_attractors
  rcases h with h | ⟨hy, hz⟩
  · exact Or.inl h
  · have heq : (fun _ : ι => c) =ᶠ[l] z :=
      Filter.Eventually.mono hz (fun _ hi => hi.symm)
    exact Or.inr ⟨hy, Filter.Tendsto.congr' heq tendsto_const_nhds⟩

end ThreeFactors
end Problem340.OrbitAttraction

end

end OAI
