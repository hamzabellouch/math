import OAI.GameTheory.SnakyTwentyOne.Model
import OAI.GameTheory.SnakyTwentyOne.Semantics.Game
import OAI.GameTheory.SnakyTwentyOne.Semantics.Geometry

namespace OAI

namespace SnakyPrototype.Certificate21
def currentCode (s : Fin 8) : Fin 8 := ![0, 1, 4, 5, 2, 3, 6, 7] s
def currentOrient (s : Fin 8) (p : Cell) : Cell :=
  match s.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (-p.1, p.2)
  | 3 => (p.2, -p.1)
  | 4 => (p.1, -p.2)
  | 5 => (-p.2, p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
theorem currentOrient_eq (s : Fin 8) (p : Cell) :
    currentOrient s p = orient (currentCode s) p := by
  fin_cases s <;> rfl
def placed21 (s : Fin 8) (t : Cell) (A : Finset Cell) : Finset Cell :=
  A.map (placementEquiv (currentCode s) t).toEmbedding
theorem placed21_eq_image (s : Fin 8) (t : Cell) (A : Finset Cell) :
    placed21 s t A = A.image (fun p => currentOrient s p + t) := by
  rw [placed21, Finset.map_eq_image]
  apply Finset.image_congr
  intro p _
  change orient (currentCode s) p + t = currentOrient s p + t
  rw [currentOrient_eq]
theorem placed21_template {n : ℕ} {A T : Finset Cell}
    (h : Template HasSnaky n A T) (s : Fin 8) (t : Cell) :
    Template HasSnaky n (placed21 s t A) (placed21 s t T) := by
  have hh := placed_template h (currentCode s) t
  simpa only [placed21, Finset.map_eq_image, Equiv.toEmbedding,
    Function.Embedding.coeFn_mk, coe_placementEquiv] using hh
def commonEnvelope {r : ℕ} (D : Fin (r + 1) → Finset Cell) : Finset Cell :=
  (D 0).filter (fun b => ∀ j, b ∈ D j)
theorem mem_commonEnvelope {r : ℕ} (D : Fin (r + 1) → Finset Cell)
    (b : Cell) (hb : ∀ j, b ∈ D j) : b ∈ commonEnvelope D :=
  Finset.mem_filter.mpr ⟨hb 0, hb⟩
theorem identity_target (M : Finset Cell) (h : snaky ⊆ M) : HasSnaky M := by
  refine ⟨0, (0, 0), ?_⟩
  have hp : placement 0 (0, 0) = id := by
    funext p
    rcases p with ⟨x, y⟩
    simp [placement, orient]
  rw [hp, Finset.image_id]
  exact h
theorem required_eq_combination {r : ℕ}
    (C D : Fin (r + 1) → Finset Cell) (p : Cell) (A : Finset Cell)
    (hp : p ∉ A)
    (hC : ∀ j, C j ⊆ insert p A)
    (hcommon : commonEnvelope D ⊆ insert p A)
    (horigin : ∀ x ∈ A, (∃ j, x ∈ C j) ∨ ∀ j, x ∈ D j) :
    A = ((Finset.univ.biUnion C) ∪ commonEnvelope D).erase p := by
  ext x
  constructor
  · intro hx
    apply Finset.mem_erase.mpr
    refine ⟨fun hxp => hp (hxp ▸ hx), ?_⟩
    rcases horigin x hx with hchild | hcommon'
    · obtain ⟨j, hj⟩ := hchild
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
    · exact Finset.mem_union_right _ (mem_commonEnvelope D x hcommon')
  · intro hx
    obtain ⟨hxp, hx⟩ := Finset.mem_erase.mp hx
    have hin : x ∈ insert p A := by
      rcases Finset.mem_union.mp hx with hchild | hcom
      · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hchild
        exact hC j hj
      · exact hcommon hcom
    exact (Finset.mem_insert.mp hin).resolve_left hxp
theorem envelope_eq_combination {r : ℕ}
    (D : Fin r → Finset Cell) (p : Cell) (T : Finset Cell)
    (hp : p ∈ T) (hD : ∀ j, D j ⊆ T)
    (horigin : ∀ x ∈ T, x = p ∨ ∃ j, x ∈ D j) :
    T = insert p (Finset.univ.biUnion D) := by
  ext x
  constructor
  · intro hx
    rcases horigin x hx with hxp | hchild
    · exact Finset.mem_insert.mpr (Or.inl hxp)
    · obtain ⟨j, hj⟩ := hchild
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
  · intro hx
    rcases Finset.mem_insert.mp hx with hxp | hchild
    · exact hxp ▸ hp
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hchild
      exact hD j hj
structure CheckedCard where
  required : Finset Cell
  envelope : Finset Cell
  height : ℕ
  required_sub_envelope : required ⊆ envelope
  height_positive : 1 ≤ height
  height_le_twenty_one : height ≤ 21
  works : Template HasSnaky height required envelope
end SnakyPrototype.Certificate21

end OAI
