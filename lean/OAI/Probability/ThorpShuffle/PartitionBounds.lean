import OAI.Probability.ThorpShuffle.ExtensionBounds

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) : YoungDiagram where
  cells := (Finset.univ.filter (· ∈ s)).image Subtype.val
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hyD : y ∈ D := by rw [← hzy]; exact z.property
    have hxD : x ∈ D := D.isLowerSet hxy hyD
    refine Finset.mem_image.mpr ⟨⟨x, hxD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply hs (show (⟨x, hxD⟩ : Cells D) ≤ z from by change x ≤ z.val; rwa [hzy])
    exact (Finset.mem_filter.mp hz).2

lemma mem_idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) (p : ℕ × ℕ) :
    p ∈ idealDiagram D s hs ↔ ∃ h : p ∈ D, (⟨p, h⟩ : Cells D) ∈ s := by
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨h, hp⟩
    exact Finset.mem_image.mpr ⟨⟨p, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

def idealCells (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Cells (idealDiagram D s hs) ≃o s where
  toFun x := ⟨⟨x.val, (mem_idealDiagram D s hs x.val).mp x.property |>.choose⟩,
    (mem_idealDiagram D s hs x.val).mp x.property |>.choose_spec⟩
  invFun x := ⟨x.val.val, (mem_idealDiagram D s hs x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

lemma idealDiagram_extensions_le (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Fintype.card (Extensions (Cells (idealDiagram D s hs))) ≤ Fintype.card (Extensions (Cells D)) := by
  rw [extensions_card_orderIso (idealCells D s hs)]
  exact extensions_card_ideal s hs

theorem exists_trimLower (D : YoungDiagram) (k : ℕ) (hk : k ≤ Fintype.card (Lower D)) :
    ∃ E : YoungDiagram, E.rowLen 0 = D.rowLen 0 ∧ Fintype.card (Lower E) = k ∧
      Fintype.card (Extensions (Cells E)) ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨e⟩ := extensions_nonempty (Lower D)
  let s : Set (Cells D) := {x | ∀ h : x.val.1 ≠ 0, (e.val ⟨x, h⟩).val < k}
  have hs : IsLowerSet s := by
    intro y x hxy hy hx
    have hy' : y.val.1 ≠ 0 := by have := hxy.1; omega
    exact lt_of_le_of_lt (e.property.monotone (show (⟨x, hx⟩ : Lower D) ≤ ⟨y, hy'⟩ from hxy)) (hy hy')
  let E := idealDiagram D s hs
  have htop : E.rowLen 0 = D.rowLen 0 := by
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
    change (0, j) ∈ idealDiagram D s hs ↔ (0, j) ∈ D
    rw [mem_idealDiagram]
    exact ⟨fun h => h.choose, fun h => ⟨h, fun hn => (hn rfl).elim⟩⟩
  let f : Lower E ≃ Fin k := {
    toFun := fun x =>
      let z := idealCells D s hs x.val
      ⟨(e.val ⟨z.val, x.property⟩).val, z.property x.property⟩
    invFun := fun j =>
      let z := e.val.symm ⟨j.val, j.isLt.trans_le hk⟩
      ⟨(idealCells D s hs).symm ⟨z.val, by
        intro h
        have hh : (⟨z.val, h⟩ : Lower D) = z := rfl
        rw [hh, Equiv.apply_symm_apply]
        exact j.isLt⟩, z.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply (idealCells D s hs).injective
      apply Subtype.ext
      have hh := e.val.symm_apply_apply ⟨(idealCells D s hs x.val).val, x.property⟩
      simpa only [OrderIso.apply_symm_apply] using congrArg Subtype.val hh
    right_inv := by
      intro j
      apply Fin.ext
      simpa only [OrderIso.apply_symm_apply] using congrArg Fin.val (e.val.apply_symm_apply ⟨j.val, j.isLt.trans_le hk⟩) }
  exact ⟨E, htop, (Fintype.card_congr f).trans (Fintype.card_fin k), idealDiagram_extensions_le D s hs⟩

theorem choose_le_extensions (D : YoungDiagram) (k : ℕ)
    (hk : k ≤ Fintype.card (Lower D)) (hL : k ≤ D.rowLen 0) :
    (D.rowLen 0).choose k ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨E, htop, hsize, hle⟩ := exists_trimLower D k hk
  have hh := choose_row_le_extensions E (by rw [hsize, htop]; exact hL)
  rw [htop, hsize] at hh
  exact hh.trans hle

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma partition_count_le_pow (n : ℕ) : Fintype.card (Nat.Partition n) ≤ 2 ^ n := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition n) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

lemma rectangle_card_le (D : YoungDiagram) (x : Cells D) :
    (x.val.1 + 1) * (x.val.2 + 1) ≤ Fintype.card (Cells D) := by
  let f : Fin (x.val.1 + 1) × Fin (x.val.2 + 1) → Cells D := fun p =>
    ⟨(p.1, p.2), D.up_left_mem (i2 := x.val.1) (j2 := x.val.2)
      (by have := p.1.isLt; omega) (by have := p.2.isLt; omega) x.property⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z : Cells D => z.val.1) hpq
    · exact congrArg (fun z : Cells D => z.val.2) hpq
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma cell_small_coord (D : YoungDiagram) (x : Cells D) :
    x.val.1 < Nat.sqrt (Fintype.card (Cells D)) ∨ x.val.2 < Nat.sqrt (Fintype.card (Cells D)) := by
  by_contra h
  push Not at h
  have hh := rectangle_card_le D x
  have hs := Nat.lt_succ_sqrt' (Fintype.card (Cells D))
  have hm := Nat.mul_le_mul (Nat.succ_le_succ h.1) (Nat.succ_le_succ h.2)
  nlinarith

lemma rowLen_le_card (D : YoungDiagram) (i : ℕ) : D.rowLen i ≤ Fintype.card (Cells D) := by
  rw [← card_row_subtype D i]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ Fintype.card (Cells D) := by
  rw [← card_column D j]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

theorem partition_count_le_sqrt_pow (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ (n + 1) ^ (2 * Nat.sqrt n) := by
  let F (p : Nat.Partition n) : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) :=
    (fun i => ⟨(ofPartition p).rowLen i, by
      have := rowLen_le_card (ofPartition p) i
      rw [card_ofPartition] at this
      omega⟩,
     fun j => ⟨(ofPartition p).colLen j, by
      have := colLen_le_card (ofPartition p) j
      rw [card_ofPartition] at this
      omega⟩)
  have hf : Function.Injective F := by
    intro p q hpq
    apply ofPartition_injective
    apply YoungDiagram.ext
    ext z
    have aux (p q : Nat.Partition n) (hpq : F p = F q) (hz : z ∈ ofPartition p) : z ∈ ofPartition q := by
      have hs := cell_small_coord (ofPartition p) ⟨z, hz⟩
      rw [card_ofPartition] at hs
      rcases hs with hs | hs
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.1 ⟨z.1, hs⟩).val) hpq
        change (ofPartition p).rowLen z.1 = (ofPartition q).rowLen z.1 at he
        apply YoungDiagram.mem_iff_lt_rowLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_rowLen.mp hz
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.2 ⟨z.2, hs⟩).val) hpq
        change (ofPartition p).colLen z.2 = (ofPartition q).colLen z.2 at he
        apply YoungDiagram.mem_iff_lt_colLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_colLen.mp hz
    exact ⟨aux p q hpq, aux q p hpq.symm⟩
  have hh := Fintype.card_le_of_injective F hf
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add] using hh

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma pow_le_choose_mul (a k : ℕ) : a ^ k ≤ (k * a).choose k := by
  let X := Fin k × Fin a
  let S := {s : Finset X // s.card = k}
  let f (v : Fin k → Fin a) : S := ⟨Finset.univ.image (fun i => (i, v i)), by
    rw [Finset.card_image_of_injective _ (by intro i j h; exact congrArg Prod.fst h), Finset.card_univ, Fintype.card_fin]⟩
  have hf : Function.Injective f := by
    intro v w hvw
    funext i
    have he := congrArg Subtype.val hvw
    have hm : (i, v i) ∈ (f w).val := by rw [← he]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hS : Fintype.card S = (k * a).choose k := by
    calc
      _ = ((Finset.univ : Finset X).powersetCard k).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext s
        simp
      _ = _ := by simp [X]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin, hS] using hh

lemma pow_le_choose_of_mul_le (a k L : ℕ) (h : a * k ≤ L) : a ^ k ≤ L.choose k := by
  exact (pow_le_choose_mul a k).trans (Nat.choose_le_choose k (by simpa only [Nat.mul_comm] using h))

lemma sub_add_one_le_choose (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : n - k + 1 ≤ n.choose k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkn
  simp only [Nat.add_sub_cancel_left]
  induction r with
  | zero => simp
  | succ r ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [show j + 1 + (r + 1) = (j + 1 + r) + 1 by omega, Nat.choose_succ_succ]
      have hp : 1 ≤ (j + 1 + r).choose j := Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero (by omega))
      simp only [Nat.succ_eq_add_one] at ih ⊢
      omega

end Thorp.Young

end

end OAI
