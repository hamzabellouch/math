import OAI.Combinatorics.ContingencyTables.Sampling.SmallEntries
import Mathlib.Algebra.BigOperators.Field
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-!
# Padding and the successful-table bijection

Padding a designated rectangle by a fixed amount gives a bijection from
original tables to enlarged-margin tables whose entries dominate the
padding. Each successful joint object therefore yields exactly one table.
-/

namespace ContingencyTables

open Finset
open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def paddedRows (r : I → ℕ) (P : I → J → ℕ) : I → ℕ := fun i => r i + ∑ j, P i j
def paddedColumns (c : J → ℕ) (P : I → J → ℕ) : J → ℕ := fun j => c j + ∑ i, P i j

def padTable {r : I → ℕ} {c : J → ℕ} (P : I → J → ℕ) (X : Table r c) :
    Table (paddedRows r P) (paddedColumns c P) :=
  ⟨fun i j => X.val i j + P i j, by
    constructor
    · intro i
      rw [sum_add_distrib, X.property.1 i]
      rfl
    · intro j
      rw [sum_add_distrib, X.property.2 j]
      rfl⟩

def unpadTable {r : I → ℕ} {c : J → ℕ} (P : I → J → ℕ)
    (Y : Table (paddedRows r P) (paddedColumns c P))
    (hY : ∀ i j, P i j ≤ Y.val i j) : Table r c := by
  refine ⟨fun i j => Y.val i j - P i j, ?_, ?_⟩
  · intro i
    have hsum := sum_congr (s₁ := (univ : Finset J)) (f := fun j => Y.val i j)
      (g := fun j => (Y.val i j - P i j) + P i j) rfl
      (fun j _ => (Nat.sub_add_cancel (hY i j)).symm)
    rw [Y.property.1 i, sum_add_distrib] at hsum
    exact Nat.add_right_cancel hsum.symm
  · intro j
    have hsum := sum_congr (s₁ := (univ : Finset I)) (f := fun i => Y.val i j)
      (g := fun i => (Y.val i j - P i j) + P i j) rfl
      (fun i _ => (Nat.sub_add_cancel (hY i j)).symm)
    rw [Y.property.2 j, sum_add_distrib] at hsum
    exact Nat.add_right_cancel hsum.symm

/-- Successful enlarged tables are in exact bijection with original tables. -/
def paddingEquiv (r : I → ℕ) (c : J → ℕ) (P : I → J → ℕ) :
    Table r c ≃ {Y : Table (paddedRows r P) (paddedColumns c P) //
      ∀ i j, P i j ≤ Y.val i j} where
  toFun := fun X => ⟨padTable P X, fun _ _ => Nat.le_add_left _ _⟩
  invFun := fun Y => unpadTable P Y.val Y.property
  left_inv := by
    intro X
    apply Subtype.ext
    funext i j
    exact Nat.add_sub_cancel _ _
  right_inv := by
    intro Y
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    exact Nat.sub_add_cancel (Y.property i j)

theorem successful_card (r : I → ℕ) (c : J → ℕ) (P : I → J → ℕ) :
    Fintype.card {Y : Table (paddedRows r P) (paddedColumns c P) //
      ∀ i j, P i j ≤ Y.val i j} = Fintype.card (Table r c) := by
  classical
  exact (Fintype.card_congr (paddingEquiv r c P)).symm

/-- The union bound as an injection with a deterministically chosen bad
cell label. This counts each bad table once, even if several entries fail. -/
theorem card_exists_le_sum {α K : Type*} [Fintype α] [Fintype K]
    (P : K → α → Prop) :
    Fintype.card {x : α // ∃ k, P k x} ≤ ∑ k, Fintype.card {x : α // P k x} := by
  classical
  let encode : {x : α // ∃ k, P k x} → Σ k, {x : α // P k x} :=
    fun x => ⟨Classical.choose x.property, x.val, Classical.choose_spec x.property⟩
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Σ k, {x : α // P k x} => z.2.val) h
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective encode hinj

section SuccessFraction

theorem fraction_not_exists {α K : Type*} [Fintype α] [Fintype K]
    (P : K → α → Prop) (E : ℝ) (hcard : (0 : ℝ) < Fintype.card α)
    (hbound : ∀ k, (Fintype.card {x : α // P k x} : ℝ) / Fintype.card α ≤ E) :
    1 - Fintype.card K * E ≤
      (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) / Fintype.card α := by
  have hunion := card_exists_le_sum P
  have hunionR : (Fintype.card {x : α // ∃ k, P k x} : ℝ) ≤
      ∑ k, (Fintype.card {x : α // P k x} : ℝ) := by
    have h : (Fintype.card {x : α // ∃ k, P k x} : ℝ) ≤
        (∑ k, Fintype.card {x : α // P k x} : ℕ) := Nat.cast_le.mpr hunion
    simpa only [Nat.cast_sum] using h
  have hbad : (Fintype.card {x : α // ∃ k, P k x} : ℝ) / Fintype.card α ≤
      Fintype.card K * E := by
    calc
      _ ≤ (∑ k, (Fintype.card {x : α // P k x} : ℝ)) / Fintype.card α :=
        div_le_div_of_nonneg_right hunionR hcard.le
      _ = ∑ k, (Fintype.card {x : α // P k x} : ℝ) / Fintype.card α :=
        Finset.sum_div _ _ _
      _ ≤ ∑ _k : K, E := sum_le_sum fun k _ => hbound k
      _ = _ := by simp
  have hpart : Fintype.card {x : α // ¬∃ k, P k x} +
      Fintype.card {x : α // ∃ k, P k x} = Fintype.card α := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  have hpartR : (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) +
      Fintype.card {x : α // ∃ k, P k x} = Fintype.card α := by exact_mod_cast hpart
  have hsum : (Fintype.card {x : α // ¬∃ k, P k x} : ℝ) / Fintype.card α +
      (Fintype.card {x : α // ∃ k, P k x} : ℝ) / Fintype.card α = 1 := by
    rw [← add_div, hpartR, div_self (ne_of_gt hcard)]
  linarith

variable [DecidableEq I] [DecidableEq J]

def largePadding (K : Finset (I × J)) (L : ℕ) : I → J → ℕ :=
  fun i j => if (i, j) ∈ K then L else 0

private theorem large_padding_good_card (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L : ℕ) :
    Fintype.card {Y : Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L)) //
      ¬∃ p : K, Y.val p.val.1 p.val.2 < L} = Fintype.card (Table r c) := by
  let P := largePadding K L
  let T := Table (paddedRows r P) (paddedColumns c P)
  have heq (Y : T) : (¬∃ p : K, Y.val p.val.1 p.val.2 < L) ↔
      ∀ i j, P i j ≤ Y.val i j := by
    constructor
    · intro hb i j
      by_cases hij : (i, j) ∈ K
      · have hn : ¬Y.val i j < L := fun h => hb ⟨⟨(i, j), hij⟩, h⟩
        simpa [P, largePadding, hij] using (show L ≤ Y.val i j by omega)
      · simp [P, largePadding, hij]
    · intro hg
      rintro ⟨p, hp⟩
      have h := hg p.val.1 p.val.2
      have hm : (p.val.1, p.val.2) ∈ K := p.property
      simp only [P, largePadding, hm, ite_true] at h
      omega
  have he : {Y : T // ¬∃ p : K, Y.val p.val.1 p.val.2 < L} ≃
      {Y : T // ∀ i j, P i j ≤ Y.val i j} := Equiv.subtypeEquivRight heq
  rw [Fintype.card_congr he]
  exact successful_card r c P

/-- The successful enlarged-table fraction is bounded using the proved
small-entry estimate and the exact padding bijection. This is the counting
part of paper 200-01's stationary-success proposition. -/
theorem padding_success_fraction (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (K : Finset (I × J)) (L U d : ℕ)
    (hd : 0 < d) (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2)
    (hU : 4 * d ≤ U) (hL : 2 * L ≤ U) :
    1 - K.card * (4 * L * (d : ℝ) ^ 3 / U) ≤
      (Fintype.card (Table r c) : ℝ) /
        Fintype.card (Table (paddedRows r (largePadding K L))
          (paddedColumns c (largePadding K L))) := by
  classical
  let P := largePadding K L
  let r' := paddedRows r P
  let c' := paddedColumns c P
  have htotal' : ∑ i, r' i = ∑ j, c' j := by
    dsimp [r', c', paddedRows, paddedColumns]
    rw [sum_add_distrib, sum_add_distrib, htotal, sum_comm (f := P)]
  let T := Table r' c'
  let bad (Y : T) : Prop := ∃ p : K, Y.val p.val.1 p.val.2 < L
  have hgood : Fintype.card {Y : T // ¬bad Y} = Fintype.card (Table r c) :=
    large_padding_good_card r c K L
  have hcard : (0 : ℝ) < Fintype.card T := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (table_nonempty r' c' htotal'))
  have hbound (p : K) :
      (Fintype.card {Y : T // Y.val p.val.1 p.val.2 < L} : ℝ) / Fintype.card T ≤
        4 * L * (d : ℝ) ^ 3 / U :=
    small_entry_probability htotal' p.val.1 p.val.2 U d L hd hrows hcols
      ((hrow p.val p.property).trans (Nat.le_add_right _ _))
      ((hcol p.val p.property).trans (Nat.le_add_right _ _)) hU hL
  have hfrac := fraction_not_exists (fun (p : K) (Y : T) => Y.val p.val.1 p.val.2 < L)
    (4 * L * (d : ℝ) ^ 3 / U) hcard (fun p => by
      simpa only [Fintype.card_eq_nat_card] using hbound p)
  simp only [Fintype.card_eq_nat_card] at hfrac hgood ⊢
  change 1 - Nat.card K * (4 * L * (d : ℝ) ^ 3 / U) ≤
    (Nat.card {Y : T // ¬bad Y} : ℝ) / Nat.card T at hfrac
  rw [hgood] at hfrac
  simpa only [Nat.card_eq_finsetCard] using hfrac

end SuccessFraction

end ContingencyTables

end OAI
