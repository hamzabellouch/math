import OAI.Geometry.HeilbronnTriangle.PlaneLines

namespace OAI

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Problem355.PlaneLineMatrices

variable {K : Type*} [Field K]

def planeRows (x : Fin 3 → K) (A : Matrix (Fin 3) (Fin 3) K)
    (hAx : A.mulVec x = 0) : Fin 3 → (PlaneLines.normalMap x).ker := fun i =>
  ⟨A i, by
    change dotProduct x (A i) = 0
    rw [dotProduct_comm]
    exact congr_fun hAx i⟩

theorem finrank_span_planeRows (x : Fin 3 → K) (A : Matrix (Fin 3) (Fin 3) K)
    (hAx : A.mulVec x = 0) :
    Module.finrank K (Submodule.span K (Set.range (planeRows x A hAx))) = A.rank := by
  let P := (PlaneLines.normalMap x).ker
  let S := Submodule.span K (Set.range (planeRows x A hAx))
  have hmap : S.map P.subtype = Submodule.span K (Set.range A.row) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  change Module.finrank K S = A.rank
  rw [← P.finrank_map_subtype_eq S, hmap, ← A.rank_eq_finrank_span_row]

theorem exists_line_containing_matrix_rows (x : Fin 3 → K) (hx : x ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) K) (hAx : A.mulVec x = 0) (hA : A.rank ≤ 1) :
    ∃ p : ℙ K (PlaneLines.normalMap x).ker,
      ∀ i, planeRows x A hAx i ∈ p.submodule := by
  apply PlaneLines.exists_line_containing_rows (PlaneLines.normal_plane_finrank x hx)
    (planeRows x A hAx)
  rwa [finrank_span_planeRows x A hAx]

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K]

def familyPiece {α ι : Type*} (T : Finset α) (row : α → ι → V)
    (p : ℙ K V) : Finset α := by
  classical
  exact T.filter fun a => ∀ i, row a i ∈ p.submodule

theorem card_family_le_lines_mul_real {α ι : Type*}
    (hV : Module.finrank K V = 2) (T : Finset α) (row : α → ι → V) (B : ℝ)
    (hlow : ∀ a ∈ T, Module.finrank K (Submodule.span K (Set.range (row a))) ≤ 1)
    (hbound : ∀ p : ℙ K V, ((familyPiece T row p).card : ℝ) ≤ B) :
    (T.card : ℝ) ≤ ((Nat.card K : ℝ) + 1) * B := by
  classical
  let : Finite V := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  let pieces (p : ℙ K V) := familyPiece T row p
  have hcover : T ⊆ Finset.univ.biUnion pieces := by
    intro a ha
    obtain ⟨p, hp⟩ := PlaneLines.exists_line_containing_rows hV (row a) (hlow a ha)
    exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, Finset.mem_filter.2 ⟨ha, hp⟩⟩
  calc
    (T.card : ℝ) ≤ (Finset.univ.biUnion pieces).card := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ p : ℙ K V, ((pieces p).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := pieces))
    _ ≤ ∑ _p : ℙ K V, B := Finset.sum_le_sum fun p _ => hbound p
    _ = ((Nat.card K : ℝ) + 1) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Fintype.card_eq_nat_card, PlaneLines.card_lines hV, Nat.cast_add, Nat.cast_one]

end Problem355.PlaneLineMatrices

end

end OAI
