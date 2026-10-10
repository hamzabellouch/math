import OAI.Combinatorics.Ryser.Construction.CoordinateCompatibility
import OAI.Combinatorics.Ryser.Construction.OrdinaryCover

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

def ActiveExceptional (data : ConfigurationData k F G) (i : G)
    (v : Vertex (k := k) data.altered) : Prop :=
  ∃ w ∈ data.retained, v ∈ exceptionalEdge data i w

def LineCapable (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F)) (i : G) :
    Vertex (k := k) data.altered → Prop
  | Sum.inl ell => ell.1 ∈ axes i
  | Sum.inr tag => tag.1 = i

def lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => LineCapable data axes i v ∧ ActiveExceptional data i v

def pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Finset (Vertex (k := k) data.altered) := by
  classical
  exact C.filter fun v => ¬ LineCapable data axes i v ∧ ActiveExceptional data i v

@[simp] theorem mem_lineResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ lineResources data axes C i ↔
      v ∈ C ∧ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [lineResources, Finset.mem_filter]

@[simp] theorem mem_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G)
    (v : Vertex (k := k) data.altered) :
    v ∈ pointResources data axes C i ↔
      v ∈ C ∧ ¬ LineCapable data axes i v ∧ ActiveExceptional data i v := by
  classical
  simp only [pointResources, Finset.mem_filter]

theorem lineResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    lineResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_lineResources data axes C i v).1 hv).1

theorem pointResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    pointResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_pointResources data axes C i v).1 hv).1

theorem lineResources_disjoint_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Disjoint (lineResources data axes C i) (pointResources data axes C i) := by
  apply Finset.disjoint_left.mpr
  intro v hl hp
  exact ((mem_pointResources data axes C i v).1 hp).2.1
    ((mem_lineResources data axes C i v).1 hl).2.1

theorem lineResources_disjoint_other_of_axis_subset
    (data : ConfigurationData k F G) (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i j : G) (hij : i ≠ j)
    (haxis : axes i ⊆ data.altered j) :
    Disjoint (lineResources data axes C i)
      (lineResources data axes C j ∪ pointResources data axes C j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hline := ((mem_lineResources data axes C i v).1 hi).2.1
  have hactive : ActiveExceptional data j v := by
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ((mem_lineResources data axes C j v).1 hj).2.2
    · exact ((mem_pointResources data axes C j v).1 hj).2.2
  obtain ⟨w, _, hw⟩ := hactive
  cases v with
  | inl ell =>
      have hinc := (ordinaryVertex_mem_exceptionalEdge_iff data j w ell).1 hw
      exact hinc.1 (haxis hline)
  | inr tag =>
      rcases tag with ⟨a, d, c⟩
      have hai : a = i := hline
      subst a
      exact specialVertex_notMem_exceptionalEdge_of_ne data i j hij w d c hw

theorem forcedPencilVertices_no_action_of_altered
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i)
    (v : Vertex (k := k) data.altered)
    (hv : v ∈ forcedPencilVertices data B (Sum.inr d)) (w : Point k) :
    v ∉ exceptionalEdge data i w := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hpencil := (mem_affinePencil (Sum.inr d) ell).1
    (Finset.mem_sdiff.mp hell).1
  have hdir : d = ell.1 := hpencil
  intro hmem
  have hnot := ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).1 hmem).1
  exact hnot (hdir ▸ hd)

section CoveredEdges

variable [Fintype G]

theorem exceptional_cover_of_vertex_cover (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G) :
    ∀ w ∈ data.retained, ∃ v ∈ C, v ∈ exceptionalEdge data i w := by
  intro w hw
  exact hC _ ((mem_hypergraph data _).2 (Or.inr ⟨i, w, hw, rfl⟩))

theorem exceptional_cover_sdiff_of_no_action (data : ConfigurationData k F G)
    (C P : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G)
    (hP : ∀ v ∈ P, ∀ w ∈ data.retained, v ∉ exceptionalEdge data i w) :
    ∀ w ∈ data.retained, ∃ v ∈ C \ P, v ∈ exceptionalEdge data i w := by
  intro w hw
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover data C hC i w hw
  refine ⟨v, Finset.mem_sdiff.mpr ⟨hvC, ?_⟩, hve⟩
  intro hvP
  exact hP v hvP w hw hve

theorem exceptional_cover_additional_of_altered
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i) :
    ∀ w ∈ data.retained,
      ∃ v ∈ C \ forcedPencilVertices data B (Sum.inr d),
        v ∈ exceptionalEdge data i w := by
  apply exceptional_cover_sdiff_of_no_action data C _ hC i
  intro v hv w _
  exact forcedPencilVertices_no_action_of_altered data B d i hd v hv w

end CoveredEdges

variable [Fintype k]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem lineCapable_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : LineCapable cfg axes i v) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  cases v with
  | inl ell =>
      have ha : ell.1 ∈ axisDirections σ (M i) := hv
      have hex : ∃ d : Direction k, (d = none ∨ d = some 0) ∧
          ell.1 = placedDirection σ (M i) d := by
        rcases (mem_axisDirections_iff σ (M i) ell.1).1 ha with h | h
        · exact ⟨none, Or.inl rfl, h⟩
        · exact ⟨some 0, Or.inr rfl, h⟩
      obtain ⟨d, hd, hdir⟩ := hex
      by_cases hactive : ∃ q ∈ Y, ordinaryVertex cfg ell ∈ exceptionalEdge cfg i q
      · obtain ⟨q, _, hq⟩ := hactive
        refine ⟨lineThrough d (cubeMap q), ?_⟩
        intro w _ hw
        exact cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i) hcop
          d hd ell hdir w q
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hw).2
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq).2
      · refine ⟨(none, 0), ?_⟩
        intro w hw hmem
        exact (hactive ⟨w, hw, hmem⟩).elim
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j = i := hv
      subst j
      refine ⟨(some ((cfg).inverseSlope i d), c), ?_⟩
      intro w _ hw
      exact (specialVertex_mem_exceptionalEdge_iff cfg i w d c).1 hw

theorem not_lineCapable_unique (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v)
    (p q : Point k) (hp : v ∈ exceptionalEdge cfg i p)
    (hq : v ∈ exceptionalEdge cfg i q) : cubeMap p = cubeMap q := by
  cases v with
  | inl ell =>
      have hp' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i p ell).1 hp
      have hq' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq
      have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hp'.1 h
        · exact hv h
      exact congrArg cubeMap
        (placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
          ell hout p q hp'.2 hq'.2)
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j ≠ i := hv
      exact (specialVertex_notMem_exceptionalEdge_of_ne cfg j i hji p d c hp).elim

theorem not_lineCapable_has_point (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v) :
    ∃ p : Point k, ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
  classical
  by_cases ha : ActiveExceptional cfg i v
  · obtain ⟨q, _, hq⟩ := ha
    refine ⟨cubeMap q, ?_⟩
    intro w _ hw
    exact not_lineCapable_unique σ M b Y X i v hv w q hw hq
  · refine ⟨(0, 0), ?_⟩
    intro w hw hmem
    exact (ha ⟨w, hw, hmem⟩).elim

theorem exceptional_resource_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  by_cases hv : LineCapable cfg axes i v
  · exact lineCapable_has_line σ M b Y X hcop i v hv
  · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
    refine ⟨lineThrough none p, ?_⟩
    intro w hw hmem
    rw [hp w hw hmem]
    exact incidence_lineThrough none p

theorem exists_line_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ L : Finset (AffineLine k), L.card ≤ C.card ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  refine ⟨C.image f, Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hv, hve⟩ := hcover w hw
  exact ⟨f v, Finset.mem_image_of_mem _ hv,
    Classical.choose_spec (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve⟩

theorem exists_mixed_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ (L : Finset (AffineLine k)) (B : Finset (Point k)),
      L.card ≤ (lineResources cfg axes C i).card ∧
      B.card ≤ (pointResources cfg axes C i).card ∧
      ∀ y ∈ Y.image cubeMap, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell := by
  classical
  have hlines : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ ell : AffineLine k, LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · obtain ⟨ell, hell⟩ := lineCapable_has_line σ M b Y X hcop i v hv
      exact ⟨ell, fun _ => hell⟩
    · exact ⟨(none, 0), fun h => (hv h).elim⟩
  have hpoints : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ p : Point k, ¬ LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · exact ⟨(0, 0), fun h => (h hv).elim⟩
    · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
      exact ⟨p, fun _ => hp⟩
  let f := fun v => Classical.choose (hlines v)
  let g := fun v => Classical.choose (hpoints v)
  refine ⟨(lineResources cfg axes C i).image f,
    (pointResources cfg axes C i).image g, Finset.card_image_le,
    Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := hcover w hw
  have hactive : ActiveExceptional cfg i v := ⟨w, hw, hve⟩
  by_cases hv : LineCapable cfg axes i v
  · exact Or.inr ⟨f v, Finset.mem_image_of_mem _
      ((mem_lineResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩),
      Classical.choose_spec (hlines v) hv w hw hve⟩
  · apply Or.inl
    rw [Classical.choose_spec (hpoints v) hv w hw hve]
    exact Finset.mem_image_of_mem _
      ((mem_pointResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩)

end RyserCoveringCounterexample.Construction

end

end OAI
