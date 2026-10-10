import OAI.Probability.ThorpShuffle.LinearExtensions

namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma extensions_card_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨c⟩ := extensions_nonempty (sᶜ : Set A)
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions s) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr e.val c.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions s) (x : s) : (F e x).val = (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions s) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (c.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions s) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact e.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (e.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (c.property hxy) _
  let f (e : Extensions s) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  simpa only [hFs] using hh

lemma extensions_card_compl_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions (sᶜ : Set A)) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions (sᶜ : Set A)) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr a.val e.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions (sᶜ : Set A)) (x : s) : (F e x).val = (a.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions (sᶜ : Set A)) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions (sᶜ : Set A)) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact a.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (a.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (e.property hxy) _
  let f (e : Extensions (sᶜ : Set A)) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  have h := congrArg (fun z : ℕ => z - Fintype.card s) hh
  simpa only [hFc, Nat.add_sub_cancel_left] using h

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma choose_le_extensions_split (s : Set A)
    (hs : ∀ x y : A, x < y → (x ∈ s ↔ y ∈ s)) :
    (Fintype.card A).choose (Fintype.card s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  obtain ⟨b⟩ := extensions_nonempty (sᶜ : Set A)
  let I := {S : Finset (Fin (Fintype.card A)) // S.card = Fintype.card s}
  have hi : Fintype.card I = (Fintype.card A).choose (Fintype.card s) := by
    calc
      Fintype.card I = ((Finset.univ : Finset (Fin (Fintype.card A))).powersetCard (Fintype.card s)).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext S
        simp
      _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let P (S : I) : Set (Fin (Fintype.card A)) := S.val
  have hP (S : I) : Fintype.card (P S) = Fintype.card s := by
    simpa [P] using S.property
  have hC (S : I) : Fintype.card ((P S)ᶜ : Set (Fin (Fintype.card A))) =
      Fintype.card (sᶜ : Set A) := by
    have h₁ := Fintype.card_congr (Equiv.Set.sumCompl (P S))
    have h₂ := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum, Fintype.card_fin, hP] at h₁ h₂
    omega
  let ea (S : I) := (Fintype.orderIsoFinOfCardEq (P S) (hP S))
  let eb (S : I) := (Fintype.orderIsoFinOfCardEq ((P S)ᶜ : Set _) (hC S))
  let F (S : I) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans
      (Equiv.sumCongr (a.val.trans (ea S).toEquiv) (b.val.trans (eb S).toEquiv))).trans
        (Equiv.Set.sumCompl (P S))
  have hFa (S : I) (x : s) : F S x = (ea S (a.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFb (S : I) (x : (sᶜ : Set A)) : F S x = (eb S (b.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hFm (S : I) (x : A) : F S x ∈ P S ↔ x ∈ s := by
    by_cases hx : x ∈ s
    · rw [hFa S ⟨x, hx⟩]
      exact iff_of_true (ea S (a.val ⟨x, hx⟩)).property hx
    · rw [hFb S ⟨x, hx⟩]
      exact iff_of_false (eb S (b.val ⟨x, hx⟩)).property hx
  have hF (S : I) : StrictMono (F S) := by
    intro x y hxy
    by_cases hx : x ∈ s
    · have hy := (hs x y hxy).mp hx
      rw [hFa S ⟨x, hx⟩, hFa S ⟨y, hy⟩]
      exact (ea S).strictMono (a.property hxy)
    · have hy : y ∉ s := fun h => hx ((hs x y hxy).mpr h)
      rw [hFb S ⟨x, hx⟩, hFb S ⟨y, hy⟩]
      exact (eb S).strictMono (b.property hxy)
  let f (S : I) : Extensions A := ⟨F S, hF S⟩
  rw [← hi]
  apply Fintype.card_le_of_injective f
  intro S T hST
  apply Subtype.ext
  ext z
  obtain ⟨x, rfl⟩ := (F S).surjective z
  have he : F S x = F T x := congrArg (fun e : Extensions A => e.val x) hST
  change F S x ∈ P S ↔ F S x ∈ P T
  rw [hFm, he, hFm]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

abbrev Lower (D : YoungDiagram) := {x : Cells D // x.val.1 ≠ 0}

def topPrefix (D : YoungDiagram) (u : ℕ) : Set (Cells D) :=
  {x | x.val.1 = 0 ∧ x.val.2 < u}

lemma topPrefix_lower (D : YoungDiagram) (u : ℕ) : IsLowerSet (topPrefix D u) := by
  intro y x hxy hy
  change y.val.1 = 0 ∧ y.val.2 < u at hy
  change x.val.1 = 0 ∧ x.val.2 < u
  exact ⟨by have := hxy.1; omega, lt_of_le_of_lt hxy.2 hy.2⟩

lemma card_topPrefix (D : YoungDiagram) (u : ℕ) (hu : u ≤ D.rowLen 0) :
    Fintype.card (topPrefix D u) = u := by
  let e : topPrefix D u ≃ Fin u := {
    toFun := fun x => ⟨x.val.val.2, x.property.2⟩
    invFun := fun j => ⟨⟨(0, j), YoungDiagram.mem_iff_lt_rowLen.mpr (j.isLt.trans_le hu)⟩, rfl, j.isLt⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.1.symm rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin u)

lemma card_lower_add (D : YoungDiagram) :
    D.rowLen 0 + Fintype.card (Lower D) = Fintype.card (Cells D) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun x : Cells D => x.val.1 = 0))
  simpa only [Fintype.card_sum, card_row_subtype] using h

lemma lower_col_lt (D : YoungDiagram) (x : Lower D) : x.val.val.2 < Fintype.card (Lower D) := by
  let f : Fin (x.val.val.2 + 1) → Lower D := fun j =>
    ⟨⟨(1, j), D.up_left_mem (i2 := x.val.val.1) (j2 := x.val.val.2) (by have := x.property; omega) (by have := j.isLt; omega) x.val.property⟩, by simp⟩
  have hf : Function.Injective f := by
    intro j k hjk
    exact Fin.ext (congrArg (fun z : Lower D => z.val.val.2) hjk)
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hh
  omega

theorem choose_row_le_extensions (D : YoungDiagram)
    (hu : Fintype.card (Lower D) ≤ D.rowLen 0) :
    (D.rowLen 0).choose (Fintype.card (Lower D)) ≤ Fintype.card (Extensions (Cells D)) := by
  let u := Fintype.card (Lower D)
  let s := topPrefix D u
  let A := (sᶜ : Set (Cells D))
  let r : Set A := {x | x.val.val.1 ≠ 0}
  have hc : Fintype.card A = D.rowLen 0 := by
    have hh := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum] at hh
    have hs : Fintype.card s = u := card_topPrefix D u hu
    have hl := card_lower_add D
    change D.rowLen 0 + u = Fintype.card (Cells D) at hl
    change Fintype.card s + Fintype.card A = Fintype.card (Cells D) at hh
    omega
  let e : r ≃ Lower D := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, fun h => x.property h.1⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hr : Fintype.card r = u := Fintype.card_congr e
  have hsplit : ∀ x y : A, x < y → (x ∈ r ↔ y ∈ r) := by
    intro x y hxy
    have h₁ := hxy.le.1
    have h₂ := hxy.le.2
    change x.val.val.1 ≠ 0 ↔ y.val.val.1 ≠ 0
    constructor
    · intro hx hy; exact hx (by omega)
    · intro hy hx
      have hcol := lower_col_lt D ⟨y.val, hy⟩
      have hp := x.property
      change ¬(x.val.val.1 = 0 ∧ x.val.val.2 < u) at hp
      change y.val.val.2 < u at hcol
      exact hp ⟨hx, lt_of_le_of_lt h₂ hcol⟩
  have hh := choose_le_extensions_split r hsplit
  have hrN : Nat.card r = u := by simpa only [Fintype.card_eq_nat_card] using hr
  have hcN : Nat.card A = D.rowLen 0 := by simpa only [Fintype.card_eq_nat_card] using hc
  have hh' : (D.rowLen 0).choose u ≤ Fintype.card (Extensions A) := by
    simpa only [Fintype.card_eq_nat_card, hrN, hcN] using hh
  exact hh'.trans (extensions_card_compl_ideal s (topPrefix_lower D u))

end Thorp.Young

end

end OAI
