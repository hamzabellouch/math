import OAI.Combinatorics.Ryser.Construction.ExceptionalCover
import OAI.Combinatorics.Ryser.Construction.CoverBudget
import OAI.Combinatorics.Ryser.Construction.GadgetConsequences

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X

theorem forced_vertex_inside_axes
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (B : Finset (AffineLine F)) (v : Vertex (k := k) (cfg).altered)
    (hv : v ∈ forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)))
    (w : Point k) (hve : v ∈ exceptionalEdge cfg i w) :
    Incidence (cubeMap w) (lineThrough none (cubeMap wp)) ∨
      Incidence (cubeMap w) (lineThrough (some 0) (cubeMap wp)) := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hwp : Incidence (placedPoint σ (M i) (b i) wp) ell :=
    (mem_affinePencil _ ell).1 (Finset.mem_sdiff.mp hell).1
  have hw := (ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hve
  by_cases haxis : ell.1 ∈ axisDirections σ (M i)
  · rcases (mem_axisDirections_iff σ (M i) ell.1).1 haxis with hd | hd
    · exact Or.inl (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop none (Or.inl rfl) ell hd w wp hw.2 hwp)
    · exact Or.inr (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop (some 0) (Or.inr rfl) ell hd w wp hw.2 hwp)
  · have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hw.1 h
      · exact haxis h
    have hsame : w = wp :=
      placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
        ell hout w wp hw.2 hwp
    subst w
    exact Or.inl (incidence_lineThrough none (cubeMap wp))

variable [Fintype G]

theorem exists_inside_axis_line_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (B : Finset (AffineLine F)) :
    ∃ L : Finset (AffineLine k),
      L.card ≤ (C \ forcedPencilVertices cfg B
        (Sum.inl (placedPoint σ (M i) (b i) wp))).card + 2 ∧
      lineThrough none (cubeMap wp) ∈ L ∧
      lineThrough (some 0) (cubeMap wp) ∈ L ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let P := forcedPencilVertices cfg B (Sum.inl (placedPoint σ (M i) (b i) wp))
  let A := C \ P
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  let vertical := lineThrough none (cubeMap wp)
  let horizontal := lineThrough (some 0) (cubeMap wp)
  let L := insert vertical (insert horizontal (A.image f))
  have hvertical : vertical ∈ L := Finset.mem_insert_self _ _
  have hhorizontal : horizontal ∈ L :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcard : L.card ≤ A.card + 2 := by
    have houter := Finset.card_insert_le vertical (insert horizontal (A.image f))
    have hinner := Finset.card_insert_le horizontal (A.image f)
    have himage : (A.image f).card ≤ A.card := Finset.card_image_le
    change (insert vertical (insert horizontal (A.image f))).card ≤ A.card + 2
    omega
  refine ⟨L, hcard, hvertical, hhorizontal, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover cfg C hC i w hw
  by_cases hvP : v ∈ P
  · rcases forced_vertex_inside_axes σ M b Y X hcop i wp B v hvP w hve with hv | hh
    · exact ⟨vertical, hvertical, hv⟩
    · exact ⟨horizontal, hhorizontal, hh⟩
  · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hvC, hvP⟩
    refine ⟨f v, Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hvA)), ?_⟩
    exact Classical.choose_spec
      (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve

theorem finite_inside_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F))
    (hforced : forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)) ⊆ C)
    (hdeleted : (B ∩ affinePencil
      (Sum.inl (placedPoint σ (M i) (b i) wp))).card ≤ Fintype.card k - 1) :
    False := by
  obtain ⟨L, hLcard, hvertical, hhorizontal, hcover⟩ :=
    exists_inside_axis_line_cover σ M b Y X hcop i wp C hC B
  have hpositive := finite_deletedPencil_card_pos cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hremaining := finite_additional_card_le cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hsmall : L.card ≤ Fintype.card k := by omega
  have hdirections : (lineThrough none (cubeMap wp)).1 ≠
      (lineThrough (some 0) (cubeMap wp)).1 := by
    simp only [lineThrough_direction, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hY.not_line_cover_of_distinct_directions L hsmall
    hvertical hhorizontal hdirections hcover

end RyserCoveringCounterexample.Construction

end OAI
