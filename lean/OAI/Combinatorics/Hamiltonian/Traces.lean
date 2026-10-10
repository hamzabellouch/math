import OAI.Combinatorics.Hamiltonian.Gluing

namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

def curve (d : G.Dart) : Path (E.point d.fst) (E.point d.snd) :=
  E.arc d.fst d.snd d.adj

@[simp] theorem curve_zero (d : G.Dart) : E.curve d 0 = E.point d.fst :=
  (E.curve d).source

@[simp] theorem curve_one (d : G.Dart) : E.curve d 1 = E.point d.snd :=
  (E.curve d).target

theorem curve_injective (d : G.Dart) : Function.Injective (E.curve d) :=
  E.arc_injective d.fst d.snd d.adj

theorem curve_symm (d : G.Dart) (t : unitInterval) :
    E.curve d.symm t = E.curve d (unitInterval.symm t) := by
  change E.arc d.snd d.fst d.adj.symm t = _
  rw [E.arc_reverse]
  rfl

theorem curve_eq_point_iff (d : G.Dart) (t : unitInterval) (v : V) :
    E.curve d t = E.point v ↔ (t = 0 ∧ v = d.fst) ∨ (t = 1 ∧ v = d.snd) := by
  constructor
  · exact E.arc_avoids_vertices d.fst d.snd d.adj t v
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem curve_eq_curve_interior {d e : G.Dart} {t s : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (h : E.curve d t = E.curve e s) : d = e ∨ d = e.symm := by
  rcases E.interiors_disjoint d.fst d.snd e.fst e.snd d.adj e.adj
    t s ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact Or.inl (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))
  · exact Or.inr (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))

private def third : unitInterval := ⟨1 / 3, by norm_num⟩
private def twoThirds : unitInterval := ⟨2 / 3, by norm_num⟩

def trace (d : G.Dart) (a b : unitInterval) : Set (ℝ × ℝ) :=
  (E.curve d) '' Set.Icc a b

theorem trace_compact (d : G.Dart) (a b : unitInterval) :
    IsCompact (E.trace d a b) :=
  isCompact_Icc.image (E.curve d).continuous

theorem trace_preconnected (d : G.Dart) (a b : unitInterval) :
    IsPreconnected (E.trace d a b) :=
  isPreconnected_Icc.image _ (E.curve d).continuous.continuousOn

def branch (v : V) : Set (ℝ × ℝ) :=
  {E.point v} ∪ ⋃ d : {d : G.Dart // d.fst = v}, E.trace d.val 0 third

def core (d : G.Dart) : Set (ℝ × ℝ) := E.trace d third twoThirds

theorem branch_point (v : V) : E.point v ∈ E.branch v :=
  Or.inl rfl

theorem branch_compact [Finite V] (v : V) : IsCompact (E.branch v) := by
  classical
  have : Finite G.Dart := Finite.of_injective SimpleGraph.Dart.toProd
    SimpleGraph.Dart.toProd_injective
  exact isCompact_singleton.union (isCompact_iUnion fun d => E.trace_compact d.val 0 third)

theorem core_compact (d : G.Dart) : IsCompact (E.core d) := E.trace_compact _ _ _

theorem core_preconnected (d : G.Dart) : IsPreconnected (E.core d) :=
  E.trace_preconnected _ _ _

private theorem initial_meeting {d e : G.Dart} {t s : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 3) (hs : (s : ℝ) ≤ 1 / 3)
    (h : E.curve d t = E.curve e s) : d.fst = e.fst := by
  have ht₁ : t ≠ 1 := by intro heq; subst t; norm_num at ht
  have hs₁ : s ≠ 1 := by intro heq; subst s; norm_num at hs
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact h.2
    · exact (hs₁ h.1).elim
  by_cases hs₀ : s = 0
  · subst s
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff d t e.fst).mp h with h | h
    · exact h.2.symm
    · exact (ht₁ h.1).elim
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with heq | heq
  · exact congrArg (fun d : G.Dart => d.fst) heq
  · subst d
    rw [E.curve_symm] at h
    have hp := congrArg Subtype.val (E.curve_injective e h)
    simp only [unitInterval.coe_symm_eq] at hp
    linarith

theorem branch_disjoint {v w : V} (hvw : v ≠ w) :
    Disjoint (E.branch v) (E.branch w) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hvw (E.point_injective (hp.symm.trans hq))
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hq
    have ha : E.curve d t = E.point v := heq.trans hp
    rcases (E.curve_eq_point_iff d t v).mp ha with ha | ha
    · exact hvw (ha.2.trans hd)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    have ha : E.curve d t = E.point w := heq.trans hq
    rcases (E.curve_eq_point_iff d t w).mp ha with ha | ha
    · exact hvw (hd.symm.trans ha.2.symm)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    obtain ⟨⟨e, he⟩, s, hs, heq'⟩ := Set.mem_iUnion.mp hq
    exact hvw (hd.symm.trans ((E.initial_meeting ht.2 hs.2 (heq.trans heq'.symm)).trans he))

private theorem middle_nonendpoint {t : unitInterval} (ht : t ∈ Set.Icc third twoThirds) :
    t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    have hh : (1 : ℝ) / 3 ≤ t := ht.1
    rw [h] at hh
    norm_num at hh
  · intro h
    have hh : (t : ℝ) ≤ 2 / 3 := ht.2
    rw [h] at hh
    norm_num at hh

theorem core_avoids_vertices (d : G.Dart) (v : V) : E.point v ∉ E.core d := by
  rintro ⟨t, ht, heq⟩
  have hn := middle_nonendpoint ht
  rcases (E.curve_eq_point_iff d t v).mp heq with h | h
  · exact hn.1 h.1
  · exact hn.2 h.1

theorem core_disjoint {d e : G.Dart} (hde : d.edge ≠ e.edge) :
    Disjoint (E.core d) (E.core e) := by
  rw [Set.disjoint_left]
  rintro p ⟨t, ht, heq⟩ ⟨s, hs, heq'⟩
  obtain ⟨ht₀, ht₁⟩ := middle_nonendpoint ht
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ (heq.trans heq'.symm) with h | h
  · exact hde (congrArg SimpleGraph.Dart.edge h)
  · exact hde ((congrArg SimpleGraph.Dart.edge h).trans e.edge_symm)

theorem branch_core_disjoint {v : V} {e : G.Dart}
    (hv₁ : v ≠ e.fst) (hv₂ : v ≠ e.snd) : Disjoint (E.branch v) (E.core e) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp
  · exact E.core_avoids_vertices e v (hp ▸ hq)
  obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
  obtain ⟨s, hs, heq'⟩ := hq
  have h : E.curve d t = E.curve e s := heq.trans heq'.symm
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  have ht₁ : t ≠ 1 := by
    intro heq
    have hh : (t : ℝ) ≤ 1 / 3 := ht.2
    rw [heq] at hh
    norm_num at hh
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact hs₀ h.1
    · exact hs₁ h.1
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact hv₁ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))
  · exact hv₂ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))

theorem branch_preconnected (v : V) : IsPreconnected (E.branch v) := by
  apply isPreconnected_of_forall (E.point v)
  intro y hy
  rcases hy with hy | hy
  · exact ⟨{E.point v}, Set.subset_union_left, rfl, hy, isPreconnected_singleton⟩
  · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hy
    refine ⟨E.trace d.val 0 third, ?_, ?_, hd, E.trace_preconnected _ _ _⟩
    · exact fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨d, hx⟩)
    · refine ⟨0, ⟨le_rfl, ?_⟩, ?_⟩
      · change (0 : ℝ) ≤ 1 / 3
        norm_num
      · simpa only [E.curve_zero] using congrArg E.point d.property

theorem branch_connected (v : V) : IsConnected (E.branch v) :=
  ⟨⟨_, E.branch_point v⟩, E.branch_preconnected v⟩

private theorem third_le_twoThirds : third ≤ twoThirds := by
  change (1 : ℝ) / 3 ≤ 2 / 3
  norm_num

private theorem symm_third : unitInterval.symm third = twoThirds := by
  apply Subtype.ext
  change 1 - (1 : ℝ) / 3 = 2 / 3
  norm_num

theorem core_connected (d : G.Dart) : IsConnected (E.core d) :=
  ⟨⟨E.curve d third, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩,
    E.core_preconnected d⟩

theorem branch_core_meets (d : G.Dart) :
    (E.branch d.fst ∩ E.core d).Nonempty ∧ (E.branch d.snd ∩ E.core d).Nonempty := by
  constructor
  · refine ⟨E.curve d third, ?_, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d, rfl⟩, third, ⟨?_, le_rfl⟩, rfl⟩)
    change (0 : ℝ) ≤ 1 / 3
    norm_num
  · refine ⟨E.curve d twoThirds, ?_, twoThirds, ⟨third_le_twoThirds, le_rfl⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d.symm, rfl⟩, third, ⟨?_, le_rfl⟩, ?_⟩)
    · change (0 : ℝ) ≤ 1 / 3
      norm_num
    · rw [E.curve_symm, symm_third]

theorem finite_positive_radius {ι : Type*} [Finite ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let _ := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, h⟩ := ih
      refine ⟨min δ (r a), lt_min hδ (hr a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  obtain ⟨δ, hδ, h⟩ := aux Finset.univ
  exact ⟨δ, hδ, fun i => h i (Finset.mem_univ i)⟩

theorem uniform_thickening {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, R i j →
      Disjoint (Metric.thickening δ (K i)) (Metric.thickening δ (K j)) := by
  classical
  let I := {p : ι × ι // R p.1 p.2}
  have hex (p : I) : ∃ δ : ℝ, 0 < δ ∧
      Disjoint (Metric.thickening δ (K p.val.1)) (Metric.thickening δ (K p.val.2)) :=
    (hR _ _ p.property).exists_thickenings (hK _) (hK _).isClosed
  choose r hr hd using hex
  obtain ⟨δ, hδ, hle⟩ := finite_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  let p : I := ⟨(i, j), hij⟩
  exact (hd p).mono (Metric.thickening_mono (hle p) _) (Metric.thickening_mono (hle p) _)

end
end Barnette.PlaneEmbedding

end OAI
