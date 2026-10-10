import OAI.Probability.ThorpShuffle.Cyclic

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young

abbrev Cells (D : YoungDiagram) := {p : ℕ × ℕ // p ∈ D.cells}

lemma fin_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have aux : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hl := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from by simp)
      have hi := ih hk'
      omega
  exact aux i.val i.isLt

lemma card_column (D : YoungDiagram) (j : ℕ) :
    (Finset.univ.filter fun x : Cells D => x.val.2 = j).card = D.colLen j := by
  classical
  let e : {x : Cells D // x.val.2 = j} ≃ Fin (D.colLen j) := {
    toFun := fun x => ⟨x.val.val.1, YoungDiagram.mem_iff_lt_colLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun i => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.symm
    right_inv := by intro i; rfl }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma card_row_subtype (D : YoungDiagram) (i : ℕ) :
    Fintype.card {x : Cells D // x.val.1 = i} = D.rowLen i := by
  let e : {x : Cells D // x.val.1 = i} ≃ Fin (D.rowLen i) := {
    toFun := fun x => ⟨x.val.val.2, YoungDiagram.mem_iff_lt_rowLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun j => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv := by intro j; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma eq_of_rowPreserving (D E : YoungDiagram) (e : Cells D ≃ Cells E)
    (he : ∀ x, (e x).val.1 = x.val.1) : D = E := by
  have hr (i : ℕ) : D.rowLen i = E.rowLen i := by
    rw [← card_row_subtype D i, ← card_row_subtype E i]
    exact Fintype.card_congr (e.subtypeEquiv (fun x => by rw [he]))
  apply YoungDiagram.ext
  ext p
  obtain ⟨i, j⟩ := p
  change (i, j) ∈ D ↔ (i, j) ∈ E
  simp only [YoungDiagram.mem_iff_lt_rowLen, hr]

theorem column_sort_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, x.val.1 ≤ r (σ x) := by
  classical
  let S (j : ℕ) : Finset ℕ := (Finset.univ.filter fun x : Cells D => x.val.2 = j).image r
  have hc (j : ℕ) : (S j).card = D.colLen j := by
    change ((Finset.univ.filter fun x : Cells D => x.val.2 = j).image r).card = _
    rw [Finset.card_image_iff.mpr (show Set.InjOn r ↑(Finset.univ.filter fun x : Cells D => x.val.2 = j) from by
      intro x hx y hy hxy
      exact hinj x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy)]
    exact card_column D j
  let F (j : ℕ) := (S j).orderEmbOfFin (hc j)
  have hpre (x : Cells D) : ∃ y : Cells D, y.val.2 = x.val.2 ∧
      r y = F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ := by
    have hm := (S x.val.2).orderEmbOfFin_mem (hc _) ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩
  choose f hcol hr using hpre
  have hf : Function.Injective f := by
    intro x y he
    have hj : x.val.2 = y.val.2 := (hcol x).symm.trans ((congrArg (fun z : Cells D => z.val.2) he).trans (hcol y))
    have hi : x.val.1 = y.val.1 := by
      have hval : F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ =
          F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ := by
        rw [← hr x, ← hr y, he]
      have hy : y.val.1 < D.colLen x.val.2 := by rw [hj]; exact YoungDiagram.mem_iff_lt_colLen.mp y.property
      have hid : F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ = F x.val.2 ⟨y.val.1, hy⟩ := by
        have aux (j k i : ℕ) (hk : j = k) (hi : i < D.colLen j) (hi' : i < D.colLen k) :
            F j ⟨i, hi⟩ = F k ⟨i, hi'⟩ := by subst k; rfl
        exact aux _ _ _ hj.symm _ _
      rw [hid] at hval
      exact congrArg Fin.val ((F x.val.2).injective hval)
    exact Subtype.ext (Prod.ext hi hj)
  let σ : Equiv.Perm (Cells D) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨σ, hcol, ?_⟩
  have hle (x : Cells D) : x.val.1 ≤ r (σ x) := by
    change x.val.1 ≤ r (f x)
    rw [hr]
    exact fin_le_strictMono _ (F x.val.2).strictMono ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
  exact hle

lemma rowRankSum_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y) :
    ∑ x : Cells D, x.val.1 ≤ ∑ x : Cells D, r x := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D r hinj
  rw [← Equiv.sum_comp σ r]
  exact Finset.sum_le_sum fun x _ => hσ x

theorem column_sort (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    (hsum : ∑ x : Cells D, r x = ∑ x : Cells D, x.val.1) :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, r (σ x) = x.val.1 := by
  obtain ⟨σ, hc, hle⟩ := column_sort_le D r hinj
  refine ⟨σ, hc, ?_⟩
  have heq : ∑ x : Cells D, x.val.1 = ∑ x : Cells D, r (σ x) := by
    rw [Equiv.sum_comp σ r, hsum]
  have hh := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun x _ => hle x)).mp heq
  intro x
  exact (hh x (Finset.mem_univ x)).symm

end Thorp.Young

end

end OAI
