import Mathlib

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite partition with a recorded set of removed separator vertices.
Edges between distinct labels must meet that set. This is only the recursive
combinatorial stage; no planar separator is supplied by this definition. -/
structure CutPartition (G : SimpleGraph V) (U : Finset V) (K : ℕ) where
  label : V → ℕ
  removed : Finset V
  removed_subset : removed ⊆ U
  small : ∀ i, (U.filter (fun x => label x = i)).card ≤ K
  edge_const : ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → x ∉ removed → y ∉ removed → label x = label y

namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ}

def trivial (h : U.card ≤ K) : CutPartition G U K where
  label := fun _ => 0
  removed := ∅
  removed_subset := Finset.empty_subset _
  small := fun i => (Finset.card_le_card (Finset.filter_subset _ _)).trans h
  edge_const := by intros; rfl

end CutPartition

def region (U : Finset V) (t : V → Fin 3) (i : Fin 3) := U.filter (fun x => t x = i)

omit [Fintype V] [DecidableEq V] in
lemma mem_region {U : Finset V} {t : V → Fin 3} {i : Fin 3} {x : V} :
    x ∈ region U t i ↔ x ∈ U ∧ t x = i := Finset.mem_filter

def vertexNumber (x : V) : ℕ := (Fintype.equivFin V x).val

omit [DecidableEq V] in
lemma vertexNumber_injective : Function.Injective (vertexNumber (V := V)) :=
  fun _ _ h => (Fintype.equivFin V).injective (Fin.ext h)

def coloredLabel (t : V → Fin 3) (p q : V → ℕ) (x : V) : ℕ :=
  if t x = 0 then 3 * vertexNumber x else if t x = 1 then 3 * p x + 1 else 3 * q x + 2

omit [DecidableEq V] in
lemma coloredLabel_mod (t : V → Fin 3) (p q : V → ℕ) (x : V) :
    coloredLabel t p q x % 3 = (t x).val := by
  have hx := (t x).isLt
  have h0 : t x = 0 ↔ (t x).val = 0 := Fin.ext_iff
  have h1 : t x = 1 ↔ (t x).val = 1 := Fin.ext_iff
  simp only [coloredLabel]
  split_ifs <;> omega

omit [DecidableEq V] in
lemma coloredLabel_tag {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (h : coloredLabel t p q x = coloredLabel t p q y) : t x = t y := by
  apply Fin.ext
  rw [← coloredLabel_mod t p q x,← coloredLabel_mod t p q y,h]

omit [DecidableEq V] in
lemma coloredLabel_zero {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 0) (h : coloredLabel t p q x = coloredLabel t p q y) : x = y := by
  have hy : t y = 0 := (coloredLabel_tag h).symm.trans hx
  simp only [coloredLabel,hx,hy,ite_true] at h
  exact vertexNumber_injective (by omega)

omit [DecidableEq V] in
lemma coloredLabel_one {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 1) (h : coloredLabel t p q x = coloredLabel t p q y) : p x = p y := by
  have hy : t y = 1 := (coloredLabel_tag h).symm.trans hx
  norm_num [coloredLabel,hx,hy] at h
  omega

omit [DecidableEq V] in
lemma coloredLabel_two {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 2) (h : coloredLabel t p q x = coloredLabel t p q y) : q x = q y := by
  have hy : t y = 2 := (coloredLabel_tag h).symm.trans hx
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [coloredLabel,hx,hy,h20,h21,ite_false] at h
  omega

omit [Fintype V] [DecidableEq V] in
/-- The three literal regions partition the carrier. -/
lemma region_card (U : Finset V) (t : V → Fin 3) :
    (region U t 0).card + (region U t 1).card + (region U t 2).card = U.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter U (Finset.univ : Finset (Fin 3)) t
  simp only [Finset.mem_univ,Finset.filter_true] at h
  simpa only [Fin.sum_univ_three,region] using h

lemma tag_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ} (t : V → Fin 3)
variable (P : CutPartition G (region U t 1) K) (Q : CutPartition G (region U t 2) K)

omit [DecidableEq V] in
lemma merge_small (hK : 0 < K) (i : ℕ) :
    (U.filter (fun x => coloredLabel t P.label Q.label x = i)).card ≤ K := by
  let F := U.filter (fun x => coloredLabel t P.label Q.label x = i)
  by_cases hF : F.Nonempty
  · obtain ⟨x,hxF⟩ := hF
    obtain ⟨hxU,hxi⟩ := Finset.mem_filter.mp hxF
    rcases tag_cases (t x) with hx | hx | hx
    · have hsub : F ⊆ {x} := by
        intro y hy
        obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_singleton.mpr (coloredLabel_zero hx (hxi.trans hyi.symm)).symm
      exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using (show 1 ≤ K by omega))
    · apply (Finset.card_le_card (show F ⊆ (region U t 1).filter (fun y => P.label y = P.label x) from ?_)).trans (P.small _)
      intro y hy
      obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
      have hxy := hxi.trans hyi.symm
      exact Finset.mem_filter.mpr ⟨mem_region.mpr ⟨hyU,(coloredLabel_tag hxy).symm.trans hx⟩,
        (coloredLabel_one hx hxy).symm⟩
    · apply (Finset.card_le_card (show F ⊆ (region U t 2).filter (fun y => Q.label y = Q.label x) from ?_)).trans (Q.small _)
      intro y hy
      obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
      have hxy := hxi.trans hyi.symm
      exact Finset.mem_filter.mpr ⟨mem_region.mpr ⟨hyU,(coloredLabel_tag hxy).symm.trans hx⟩,
        (coloredLabel_two hx hxy).symm⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ K
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- One literal recursive step: every separator vertex becomes a singleton,
while the two nonadjacent sides retain their recursively constructed parts. -/
def merge (hK : 0 < K)
    (hsep : ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬ G.Adj x y) :
    CutPartition G U K where
  label := coloredLabel t P.label Q.label
  removed := region U t 0 ∪ P.removed ∪ Q.removed
  removed_subset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact (mem_region.mp hx).1
      · exact (mem_region.mp (P.removed_subset hx)).1
    · exact (mem_region.mp (Q.removed_subset hx)).1
  small := merge_small t P Q hK
  edge_const := by
    intro x hxU y hyU hxy hxR hyR
    have hxr : x ∉ region U t 0 ∧ x ∉ P.removed ∧ x ∉ Q.removed := by
      simpa only [Finset.mem_union,not_or,and_assoc] using hxR
    have hyr : y ∉ region U t 0 ∧ y ∉ P.removed ∧ y ∉ Q.removed := by
      simpa only [Finset.mem_union,not_or,and_assoc] using hyR
    have hx0 : t x ≠ 0 := fun h => hxr.1 (mem_region.mpr ⟨hxU,h⟩)
    have hy0 : t y ≠ 0 := fun h => hyr.1 (mem_region.mpr ⟨hyU,h⟩)
    rcases (tag_cases (t x)).resolve_left hx0 with hx | hx
    <;> rcases (tag_cases (t y)).resolve_left hy0 with hy | hy
    · have h := P.edge_const x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy hxr.2.1 hyr.2.1
      simp [coloredLabel,hx,hy,h]
    · exact (hsep x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy).elim
    · exact (hsep y (mem_region.mpr ⟨hyU,hy⟩) x (mem_region.mpr ⟨hxU,hx⟩) hxy.symm).elim
    · have h := Q.edge_const x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy hxr.2.2 hyr.2.2
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [coloredLabel,hx,hy,h20,h21,ite_false,h]

lemma merge_removed_card (hK : 0 < K)
    (hsep : ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬ G.Adj x y) :
    (merge t P Q hK hsep).removed.card ≤
      (region U t 0).card + P.removed.card + Q.removed.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)

end CutPartition
end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
