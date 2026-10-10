import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340

section Cylinders

variable {X Y ι A : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype ι] [DecidableEq ι]

def clockMainCylinder (x₀ : X) (y₀ : Y) (i : ι) : Set (X × (ι → Y)) :=
  {p | p.1 = x₀ ∧ p.2 i = y₀}

def sphereVectorCylinder (v₀ : ι → Y) : Set (X × (ι → Y)) :=
  {p | p.2 = v₀}

lemma infDist_clockMainCylinder_le (p : X × (ι → Y)) (x₀ : X) (y₀ : Y) (i : ι) :
    Metric.infDist p (clockMainCylinder x₀ y₀ i) ≤
      max (dist p.1 x₀) (dist (p.2 i) y₀) := by
  have hmem : (x₀, Function.update p.2 i y₀) ∈ clockMainCylinder x₀ y₀ i := by
    simp [clockMainCylinder]
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [Prod.dist_eq]
  apply max_le_max le_rfl
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  by_cases hk : k = i
  · subst k
    simp
  · simp [Function.update_of_ne hk, dist_nonneg]

omit [DecidableEq ι] in
lemma infDist_sphereVectorCylinder_le (p : X × (ι → Y)) (v₀ : ι → Y) :
    Metric.infDist p (sphereVectorCylinder (X := X) v₀) ≤ dist p.2 v₀ := by
  have hmem : (p.1, v₀) ∈ sphereVectorCylinder (X := X) v₀ := rfl
  simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
    (Metric.infDist_le_dist_of_mem (x := p) hmem)

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] [Fintype ι] [DecidableEq ι] in
lemma clockMainCylinder_nonempty (x₀ : X) (y₀ : Y) (i : ι) :
    (clockMainCylinder x₀ y₀ i).Nonempty :=
  ⟨(x₀, fun _ => y₀), rfl, rfl⟩

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] [Fintype ι] [DecidableEq ι] in
lemma sphereVectorCylinder_nonempty (x₀ : X) (v₀ : ι → Y) :
    (sphereVectorCylinder (X := X) v₀).Nonempty := ⟨(x₀, v₀), rfl⟩

theorem tendsto_infDist_clockMainCylinder {l : Filter A}
    (p : A → X × (ι → Y)) (x₀ : X) (y₀ : Y) (i : ι)
    (hx : Tendsto (fun a => (p a).1) l (𝓝 x₀))
    (hy : Tendsto (fun a => (p a).2 i) l (𝓝 y₀)) :
    Tendsto (fun a => Metric.infDist (p a) (clockMainCylinder x₀ y₀ i)) l (𝓝 0) := by
  have hx' : Tendsto (fun a => dist (p a).1 x₀) l (𝓝 0) := by
    simpa using hx.dist (show Tendsto (fun _ : A => x₀) l (𝓝 x₀) from tendsto_const_nhds)
  have hy' : Tendsto (fun a => dist ((p a).2 i) y₀) l (𝓝 0) := by
    simpa using hy.dist (show Tendsto (fun _ : A => y₀) l (𝓝 y₀) from tendsto_const_nhds)
  exact squeeze_zero (fun _ => Metric.infDist_nonneg)
    (fun a => infDist_clockMainCylinder_le (p a) x₀ y₀ i)
    (by simpa using hx'.max hy')

omit [DecidableEq ι] in

theorem tendsto_infDist_sphereVectorCylinder {l : Filter A}
    (p : A → X × (ι → Y)) (v₀ : ι → Y)
    (hy : ∀ i, Tendsto (fun a => (p a).2 i) l (𝓝 (v₀ i))) :
    Tendsto (fun a => Metric.infDist (p a) (sphereVectorCylinder (X := X) v₀))
      l (𝓝 0) := by
  have hv : Tendsto (fun a => (p a).2) l (𝓝 v₀) := tendsto_pi_nhds.mpr hy
  have hd : Tendsto (fun a => dist (p a).2 v₀) l (𝓝 0) := by
    simpa using hv.dist (show Tendsto (fun _ : A => v₀) l (𝓝 v₀) from tendsto_const_nhds)
  exact squeeze_zero (fun _ => Metric.infDist_nonneg)
    (fun a => infDist_sphereVectorCylinder_le (p a) v₀) hd

theorem tendsto_infDist_attractor_union_of_coordinates {l : Filter A}
    (p : A → X × (ι → Y)) (x₀ : X) (y₀ : Y) (i : ι) (v₀ : ι → Y)
    (h : (Tendsto (fun a => (p a).1) l (𝓝 x₀) ∧
        Tendsto (fun a => (p a).2 i) l (𝓝 y₀)) ∨
      (∀ k, Tendsto (fun a => (p a).2 k) l (𝓝 (v₀ k)))) :
    Tendsto (fun a => Metric.infDist (p a)
      (clockMainCylinder x₀ y₀ i ∪ sphereVectorCylinder v₀)) l (𝓝 0) := by
  rcases h with ⟨hx, hy⟩ | hv
  · exact squeeze_zero (fun _ => Metric.infDist_nonneg)
      (fun _ => Metric.infDist_le_infDist_of_subset Set.subset_union_left
        (clockMainCylinder_nonempty x₀ y₀ i))
      (tendsto_infDist_clockMainCylinder p x₀ y₀ i hx hy)
  · exact squeeze_zero (fun _ => Metric.infDist_nonneg)
      (fun _ => Metric.infDist_le_infDist_of_subset Set.subset_union_right
        (sphereVectorCylinder_nonempty x₀ v₀))
      (tendsto_infDist_sphereVectorCylinder p v₀ hv)

omit [PseudoMetricSpace X] [Fintype ι] in

theorem tendsto_sphereVector_of_main_and_eventual_reset {l : Filter A}
    (p : A → X × (ι → Y)) (y₀ yInf : Y) (i : ι)
    (hmain : Tendsto (fun a => (p a).2 i) l (𝓝 yInf))
    (hreset : ∀ k, k ≠ i → ∀ᶠ a in l, (p a).2 k = y₀) :
    ∀ k, Tendsto (fun a => (p a).2 k) l
      (𝓝 ((Function.update (fun _ : ι => y₀) i yInf) k)) := by
  intro k
  by_cases hk : k = i
  · subst k
    simpa using hmain
  · have ht : Tendsto (fun a => (p a).2 k) l (𝓝 y₀) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [hreset k hk] with a ha using ha.symm)
    simpa [Function.update_of_ne hk] using ht

omit [Fintype ι] [DecidableEq ι] in
lemma isClosed_clockMainCylinder [T2Space X] [T2Space Y]
    (x₀ : X) (y₀ : Y) (i : ι) : IsClosed (clockMainCylinder x₀ y₀ i) := by
  exact (isClosed_eq continuous_fst continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)

omit [Fintype ι] [DecidableEq ι] in
lemma isClosed_sphereVectorCylinder [T2Space Y] (v₀ : ι → Y) :
    IsClosed (sphereVectorCylinder (X := X) v₀) :=
  isClosed_eq continuous_snd continuous_const

omit [Fintype ι] [DecidableEq ι] in
lemma isCompact_attractor_union [T2Space X] [T2Space Y]
    [CompactSpace X] [CompactSpace Y]
    (x₀ : X) (y₀ : Y) (i : ι) (v₀ : ι → Y) :
    IsCompact (clockMainCylinder x₀ y₀ i ∪ sphereVectorCylinder v₀) :=
  ((isClosed_clockMainCylinder x₀ y₀ i).union
    (isClosed_sphereVectorCylinder v₀)).isCompact

end Cylinders

theorem eventually_mem_of_tendsto_infDist_zero
    {X A : Type*} [PseudoMetricSpace X] {l : Filter A}
    {K V : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : IsOpen V) (hKV : K ⊆ V) (p : A → X)
    (h : Tendsto (fun a => Metric.infDist (p a) K) l (𝓝 0)) :
    ∀ᶠ a in l, p a ∈ V := by
  have hn : Tendsto p l (𝓝ˢ K) := (Metric.tendsto_nhdsSet hK hne).mpr (by
    intro ε hε
    exact h.eventually (Iio_mem_nhds hε))
  exact hn.eventually (hV.mem_nhdsSet.mpr hKV)

theorem counterexample_attraction_of_coordinate_alternatives
    {q : ℕ} (p : ℕ → CounterexampleManifold q)
    (clock₀ : StandardClock) (sphere₀ sphereInf : StandardSphere2)
    (i : Fin (q + 1))
    (h : (Tendsto (fun n => (p n).1) atTop (𝓝 clock₀) ∧
        Tendsto (fun n => (p n).2 i) atTop (𝓝 sphere₀)) ∨
      (Tendsto (fun n => (p n).2 i) atTop (𝓝 sphereInf) ∧
        ∀ k, k ≠ i → ∀ᶠ n in atTop, (p n).2 k = sphere₀)) :
    Tendsto (fun n => Metric.infDist (p n)
      (clockMainCylinder clock₀ sphere₀ i ∪
        sphereVectorCylinder (Function.update (fun _ => sphere₀) i sphereInf)))
      atTop (𝓝 0) := by
  apply tendsto_infDist_attractor_union_of_coordinates
  rcases h with hzero | ⟨hmain, hreset⟩
  · exact Or.inl hzero
  · exact Or.inr (tendsto_sphereVector_of_main_and_eventual_reset
      p sphere₀ sphereInf i hmain hreset)

lemma counterexample_attractor_isCompact (q : ℕ)
    (clock₀ : StandardClock) (sphere₀ sphereInf : StandardSphere2)
    (i : Fin (q + 1)) :
    IsCompact (clockMainCylinder clock₀ sphere₀ i ∪
      sphereVectorCylinder (Function.update (fun _ => sphere₀) i sphereInf)) :=
  isCompact_attractor_union clock₀ sphere₀ i _

theorem counterexample_eventually_mem_attractor_neighborhood
    {q : ℕ} (p : ℕ → CounterexampleManifold q)
    (clock₀ : StandardClock) (sphere₀ sphereInf : StandardSphere2)
    (i : Fin (q + 1))
    (h : (Tendsto (fun n => (p n).1) atTop (𝓝 clock₀) ∧
        Tendsto (fun n => (p n).2 i) atTop (𝓝 sphere₀)) ∨
      (Tendsto (fun n => (p n).2 i) atTop (𝓝 sphereInf) ∧
        ∀ k, k ≠ i → ∀ᶠ n in atTop, (p n).2 k = sphere₀))
    (V : Set (CounterexampleManifold q)) (hV : IsOpen V)
    (hsub : clockMainCylinder clock₀ sphere₀ i ∪
      sphereVectorCylinder (Function.update (fun _ => sphere₀) i sphereInf) ⊆ V) :
    ∀ᶠ n in atTop, p n ∈ V := by
  apply eventually_mem_of_tendsto_infDist_zero
    (counterexample_attractor_isCompact q clock₀ sphere₀ sphereInf i)
    ((clockMainCylinder_nonempty clock₀ sphere₀ i).mono Set.subset_union_left)
    hV hsub p
  exact counterexample_attraction_of_coordinate_alternatives
    p clock₀ sphere₀ sphereInf i h

end Problem340

end

end OAI
