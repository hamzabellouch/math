import Mathlib

namespace OAI

open Set MeasureTheory

noncomputable section

namespace TriangularLipschitz

abbrev Vertex := ℤ × ℤ

def Adj (x y : Vertex) : Prop :=
  y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
  y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) ∨
  y = (x.1 + 1, x.2 - 1) ∨ y = (x.1 - 1, x.2 + 1)

def boxIndex (ℓ : ℕ) (x : Vertex) : Vertex := (x.1 / (ℓ:ℤ), x.2 / (ℓ:ℤ))

def centralBox (ℓ : ℕ) (z : Vertex) : Finset Vertex :=
  Finset.Ico (z.1 * ℓ) ((z.1+1)*ℓ) ×ˢ Finset.Ico (z.2*ℓ) ((z.2+1)*ℓ)

lemma centralBox_card (ℓ : ℕ) (z : Vertex) : (centralBox ℓ z).card = ℓ^2 := by
  simp [centralBox, Finset.card_product, Int.card_Ico, add_mul]
  ring

lemma boxIndex_mem (ℓ : ℕ) (hℓ : 0 < ℓ) (x : Vertex) : x ∈ centralBox ℓ (boxIndex ℓ x) := by
  have hp : (0:ℤ) < ℓ := by exact_mod_cast hℓ
  have h1 := Int.emod_nonneg x.1 (ne_of_gt hp)
  have h2 := Int.emod_lt_of_pos x.1 hp
  have h3 := Int.emod_nonneg x.2 (ne_of_gt hp)
  have h4 := Int.emod_lt_of_pos x.2 hp
  have e1 := Int.emod_add_ediv_mul x.1 (ℓ:ℤ)
  have e2 := Int.emod_add_ediv_mul x.2 (ℓ:ℤ)
  simp only [centralBox, boxIndex, Finset.mem_product, Finset.mem_Ico]
  constructor <;> constructor <;> nlinarith

lemma ediv_neighbor (a b : ℤ) (ℓ : ℕ) (hℓ : 0 < ℓ) (hab : |a-b| ≤ 1) :
    |a/(ℓ:ℤ) - b/(ℓ:ℤ)| ≤ 1 := by
  have hp : (1:ℤ) ≤ ℓ := by exact_mod_cast hℓ
  have hma := Int.emod_nonneg a (by omega : (ℓ:ℤ) ≠ 0)
  have hmb := Int.emod_nonneg b (by omega : (ℓ:ℤ) ≠ 0)
  have hLa := Int.emod_lt_of_pos a (by omega : (0:ℤ) < ℓ)
  have hLb := Int.emod_lt_of_pos b (by omega : (0:ℤ) < ℓ)
  have ea := Int.emod_add_ediv_mul a (ℓ:ℤ)
  have eb := Int.emod_add_ediv_mul b (ℓ:ℤ)
  rw [abs_le] at hab ⊢
  constructor
  · by_contra hh
    have hd : a/(ℓ:ℤ) - b/(ℓ:ℤ) ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_right hd (by omega : (0:ℤ) ≤ ℓ)
    nlinarith
  · by_contra hh
    have hd : 2 ≤ a/(ℓ:ℤ) - b/(ℓ:ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_right hd (by omega : (0:ℤ) ≤ ℓ)
    nlinarith

lemma adj_boxIndex (ℓ : ℕ) (hℓ : 0 < ℓ) {x y : Vertex} (hxy : Adj x y) :
    |(boxIndex ℓ x).1-(boxIndex ℓ y).1| ≤ 1 ∧
    |(boxIndex ℓ x).2-(boxIndex ℓ y).2| ≤ 1 := by
  have hc : |x.1-y.1| ≤ 1 ∧ |x.2-y.2| ≤ 1 := by
    rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
    simp only [Adj, Prod.mk.injEq] at hxy
    simp only [abs_le]
    omega
  exact ⟨ediv_neighbor _ _ ℓ hℓ hc.1, ediv_neighbor _ _ ℓ hℓ hc.2⟩

def boxNeighborSet (z : Vertex) : Finset Vertex :=
  ((Finset.Icc (z.1-1) (z.1+1)) ×ˢ (Finset.Icc (z.2-1) (z.2+1))).erase z

lemma boxNeighborSet_card (z : Vertex) : (boxNeighborSet z).card = 8 := by
  have hz : z ∈ ((Finset.Icc (z.1-1) (z.1+1)) ×ˢ (Finset.Icc (z.2-1) (z.2+1))) := by
    simp
  rw [boxNeighborSet, Finset.card_erase_of_mem hz, Finset.card_product]
  simp only [Int.card_Icc]
  norm_num [show z.1+1+1-(z.1-1) = 3 by ring, show z.2+1+1-(z.2-1) = 3 by ring]

lemma mem_boxNeighborSet {z w : Vertex} : w ∈ boxNeighborSet z ↔
    w ≠ z ∧ |z.1-w.1| ≤ 1 ∧ |z.2-w.2| ≤ 1 := by
  simp only [boxNeighborSet, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, abs_le]
  constructor <;> intro h <;> exact ⟨h.1,by omega,by omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def boxSet (loc : V ↪ Vertex) (ℓ : ℕ) : Finset Vertex :=
  Finset.univ.image (fun x => boxIndex ℓ (loc x))

abbrev Boxes (loc : V ↪ Vertex) (ℓ : ℕ) := {z : Vertex // z ∈ boxSet loc ℓ}

noncomputable def boxMap (loc : V ↪ Vertex) (ℓ : ℕ) (x : V) : Boxes loc ℓ :=
  ⟨boxIndex ℓ (loc x), Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

noncomputable def coverGraph (loc : V ↪ Vertex) (ℓ : ℕ) : SimpleGraph (Boxes loc ℓ) where
  Adj z w := w.1 ∈ boxNeighborSet z.1
  symm := ⟨by
    intro z w hz
    rw [mem_boxNeighborSet] at hz ⊢
    exact ⟨hz.1.symm, by simpa [abs_sub_comm] using hz.2.1,
      by simpa [abs_sub_comm] using hz.2.2⟩⟩
  loopless := ⟨by intro z hz; exact (mem_boxNeighborSet.mp hz).1 rfl⟩

omit [DecidableEq V] in
lemma boxMap_adjacent (loc : V ↪ Vertex) (ℓ : ℕ) (hℓ : 0 < ℓ)
    {x y : V} (hxy : Adj (loc x) (loc y)) :
    boxMap loc ℓ x = boxMap loc ℓ y ∨
      (coverGraph loc ℓ).Adj (boxMap loc ℓ x) (boxMap loc ℓ y) := by
  by_cases he : boxIndex ℓ (loc x) = boxIndex ℓ (loc y)
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr ((mem_boxNeighborSet).mpr ⟨Ne.symm he, adj_boxIndex ℓ hℓ hxy⟩)

omit [DecidableEq V] in
lemma boxMap_fiber (loc : V ↪ Vertex) (ℓ : ℕ) (hℓ : 0 < ℓ) (w : Boxes loc ℓ) :
    (Finset.univ.filter fun x => boxMap loc ℓ x = w).card ≤ ℓ^2 := by
  classical
  rw [← centralBox_card ℓ w]
  apply Finset.card_le_card_of_injOn loc
  · intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have he' : boxIndex ℓ (loc x) = w := congrArg Subtype.val he
    rw [← he']
    exact boxIndex_mem ℓ hℓ (loc x)
  · exact fun _ _ _ _ h => loc.injective h

noncomputable def coverNeighbors (loc : V ↪ Vertex) (ℓ : ℕ) (w : Boxes loc ℓ) :
    Finset (Boxes loc ℓ) := by
  classical
  exact Finset.univ.filter fun z => (coverGraph loc ℓ).Adj w z

omit [DecidableEq V] in
lemma coverGraph_degree (loc : V ↪ Vertex) (ℓ : ℕ) (w : Boxes loc ℓ) :
    (coverNeighbors loc ℓ w).card ≤ 8 := by
  classical
  rw [coverNeighbors, ← boxNeighborSet_card w]
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact fun _ _ _ _ h => Subtype.ext h

def steps : Finset Vertex := {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)}

lemma steps_card : steps.card = 6 := by decide

lemma adj_iff_steps (x y : Vertex) : Adj x y ↔ y - x ∈ steps := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [Adj, steps, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Prod.sub_def]
  omega

omit [Fintype V] [DecidableEq V] in
lemma finite_graph_degree (loc : V ↪ Vertex) (G : SimpleGraph V)
    (hG : ∀ x y, G.Adj x y → Adj (loc x) (loc y)) (x : V)
    (T : Finset V) (hT : ∀ y ∈ T, G.Adj x y) : T.card ≤ 6 := by
  rw [← steps_card]
  apply Finset.card_le_card_of_injOn (fun y => loc y - loc x)
  · intro y hy
    exact (adj_iff_steps _ _).mp (hG x y (hT y hy))
  · intro y hy z hz he
    apply loc.injective
    exact sub_left_injective he

end TriangularLipschitz

end

end OAI
