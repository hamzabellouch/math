import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

abbrev Cell (μ : YoungDiagram) := {c // c ∈ μ.cells}
def row {μ : YoungDiagram} (x : Cell μ) : ℕ := x.val.1
def col {μ : YoungDiagram} (x : Cell μ) : ℕ := x.val.2

lemma nat_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < n := by omega
    have hl := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ from by simp)
    have hp := ih hi'
    change i ≤ f ⟨i, hi'⟩ at hp
    change i + 1 ≤ f ⟨i+1, hi⟩
    omega

lemma sum_orderEmb (s : Finset ℕ) :
    ∑ i : Fin s.card, s.orderEmbOfFin rfl i = ∑ i ∈ s, i := by
  have h := Finset.sum_map (s := (Finset.univ : Finset (Fin s.card)))
    (s.orderEmbOfFin rfl).toEmbedding (fun i : ℕ => i)
  rw [s.map_orderEmbOfFin_univ rfl] at h
  exact h.symm

lemma range_sum_le (s : Finset ℕ) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, i := by
  let e := s.orderEmbOfFin rfl
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => nat_le_strictMono e e.strictMono i)
  simpa only [← Fin.sum_univ_eq_sum_range, e, sum_orderEmb] using h

lemma eq_range_of_sum_eq (s : Finset ℕ)
    (h : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i) : s = Finset.range s.card := by
  let e := s.orderEmbOfFin rfl
  have he : ∀ i : Fin s.card, e i = i.val := by
    have hsum : ∑ i : Fin s.card, i.val = ∑ i : Fin s.card, e i := by
      dsimp only [e]
      rw [sum_orderEmb, Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact h.symm
    have hh := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin s.card) _ => nat_le_strictMono e e.strictMono i)).mp hsum
    exact fun i => (hh i (Finset.mem_univ i)).symm
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (s.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range e)
    rw [← hj, he]
    exact Finset.mem_range.mpr j.isLt
  · intro hi
    let j : Fin s.card := ⟨i, Finset.mem_range.mp hi⟩
    rw [← show e j = i from he j]
    exact s.orderEmbOfFin_mem rfl j

def columnCells (μ : YoungDiagram) (j : ℕ) : Finset (Cell μ) :=
  Finset.univ.filter (fun x => col x = j)

lemma mem_columnCells {μ : YoungDiagram} {j : ℕ} {x : Cell μ} :
    x ∈ columnCells μ j ↔ col x = j := by simp [columnCells]

lemma row_injectiveOn_column (μ : YoungDiagram) (j : ℕ) :
    Set.InjOn (row (μ := μ)) (↑(columnCells μ j) : Set (Cell μ)) := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext hxy
  exact (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm

lemma image_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).image row = Finset.range (μ.colLen j) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := x.property
    have hj := mem_columnCells.mp hx
    change x.val.2 = j at hj
    rw [← hj]
    exact YoungDiagram.mem_iff_lt_colLen.mp hc
  · intro hi
    refine ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr hi⟩, ?_, rfl⟩
    exact mem_columnCells.mpr rfl

lemma card_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).card = μ.colLen j := by
  rw [← Finset.card_image_of_injOn (row_injectiveOn_column μ j), image_row_columnCells]
  exact Finset.card_range _

lemma sum_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    ∑ x ∈ columnCells μ j, row x = ∑ i ∈ Finset.range (μ.colLen j), i := by
  rw [← image_row_columnCells μ j]
  exact (Finset.sum_image (f := fun i : ℕ => i) (row_injectiveOn_column μ j)).symm

lemma sum_columnCells_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ∑ x ∈ columnCells μ j, row x ≤ ∑ x ∈ columnCells μ j, f x := by
  have h := range_sum_le ((columnCells μ j).image f)
  rw [Finset.card_image_of_injOn hf, card_columnCells, Finset.sum_image hf] at h
  rwa [sum_row_columnCells]

lemma column_image_of_total_sum (μ : YoungDiagram) (f : Cell μ → ℕ)
    (hf : ∀ j, Set.InjOn f (columnCells μ j))
    (hsum : ∑ x, f x = ∑ x : Cell μ, row x) (j : ℕ) :
    (columnCells μ j).image f = Finset.range (μ.colLen j) := by
  classical
  let J := (Finset.univ : Finset (Cell μ)).image col
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Cell μ)), col x ∈ J := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfib (g : Cell μ → ℕ) :
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to hmaps g
  have heq : ∑ j ∈ J, ∑ x ∈ columnCells μ j, row x =
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, f x := by rw [hfib, hfib, hsum]
  have hone := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ J) => sum_columnCells_le μ f j (hf j))).mp heq
  by_cases hj : j ∈ J
  · have hc : ((columnCells μ j).image f).card = μ.colLen j := by
      rw [Finset.card_image_of_injOn (hf j), card_columnCells]
    have h : ∑ i ∈ (columnCells μ j).image f, i =
        ∑ i ∈ Finset.range ((columnCells μ j).image f).card, i := by
      rw [hc, Finset.sum_image (hf j), ← sum_row_columnCells]
      exact (hone j hj).symm
    simpa only [hc] using eq_range_of_sum_eq _ h
  · have hc : columnCells μ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hj
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, mem_columnCells.mp hx⟩
    have hz : μ.colLen j = 0 := by rw [← card_columnCells, hc]; rfl
    simp [hc, hz]

lemma rearranged_row_mem (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) (x : Cell μ) :
    (row (π x), col x) ∈ μ := by
  have he := column_image_of_total_sum μ (fun x => row (π x)) hc
    (Equiv.sum_comp π row) (col x)
  have hm : row (π x) ∈ (columnCells μ (col x)).image (fun x => row (π x)) :=
    Finset.mem_image.mpr ⟨x, mem_columnCells.mpr rfl, rfl⟩
  rw [he, Finset.mem_range] at hm
  exact YoungDiagram.mem_iff_lt_colLen.mpr hm

def fiberStabilizer {X Y : Type*} (f : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {π | ∀ x, f (π x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro a b ha hb x; exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ x)
    simpa using h.symm

abbrev rowStabilizer (μ : YoungDiagram) := fiberStabilizer (row (μ := μ))
abbrev colStabilizer (μ : YoungDiagram) := fiberStabilizer (col (μ := μ))

lemma row_col_intersection (μ : YoungDiagram) :
    rowStabilizer μ ⊓ colStabilizer μ = ⊥ := by
  apply le_antisymm
  · intro π hπ
    change π = 1
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (hπ.1 x) (hπ.2 x)
  · exact bot_le

theorem row_col_factorization (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) :
    ∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c := by
  let t : Cell μ → Cell μ := fun x =>
    ⟨(row (π x), col x), rearranged_row_mem μ π hc x⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have hcol := congrArg (fun z : Cell μ => col z) hxy
    change col x = col y at hcol
    have hrow := congrArg (fun z : Cell μ => row z) hxy
    change row (π x) = row (π y) at hrow
    exact hc (col x) (mem_columnCells.mpr rfl) (mem_columnCells.mpr hcol.symm) hrow
  let c : Equiv.Perm (Cell μ) := Equiv.ofBijective t
    ⟨ht, (Finite.injective_iff_surjective).mp ht⟩
  have cc : c ∈ colStabilizer μ := by intro x; rfl
  have cr : ∀ x, row (c x) = row (π x) := by intro x; rfl
  refine ⟨π * c⁻¹, ?_, c, cc, ?_⟩
  · intro x
    change row (π (c⁻¹ x)) = row x
    rw [← cr]
    simp
  · simp

theorem row_col_alternative (μ : YoungDiagram) (π : Equiv.Perm (Cell μ)) :
    (∃ x y : Cell μ, x ≠ y ∧ col x = col y ∧ row (π x) = row (π y)) ∨
    (∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c) := by
  by_cases hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)
  · exact Or.inr (row_col_factorization μ π hc)
  · left
    simp only [Set.InjOn] at hc
    push Not at hc
    obtain ⟨j, x, hx, y, hy, hrow, hne⟩ := hc
    exact ⟨x, y, hne, (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm, hrow⟩

end BinaryCoordinateSweeps.Young

end

end OAI
