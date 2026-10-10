import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Sum
import Lean.Elab.Tactic.Omega
import OAI.Combinatorics.ProgressionColoring.OuterRowsMod

namespace OAI

/-!
# Balanced rows for bounded-multiplicity words

Order each label fibre consecutively, then distribute the resulting enumeration
cyclically among the rows. This proves the row decomposition used in the first
family of outer-coloring tests, without assuming a balanced decomposition.
-/

universe uBeta uA uAlpha uIndex

namespace QuantitativeVanDerWaerden

open scoped BigOperators

noncomputable section

variable {β : Type uBeta} [Fintype β]

/-- Labels occurring before `b` in a fixed enumeration. -/
def earlierLabels (b : β) : Finset β := by
  classical
  exact Finset.univ.filter fun a => Fintype.equivFin β a < Fintype.equivFin β b

/-- Starting index of the block belonging to `b`. -/
def blockOffset (c : β → ℕ) (b : β) : ℕ :=
  ∑ a ∈ earlierLabels b, c a

theorem blockOffset_add_le_total (c : β → ℕ) (b : β) :
    blockOffset c b + c b ≤ ∑ a, c a := by
  classical
  have hb : b ∉ earlierLabels b := by simp [earlierLabels]
  calc
    blockOffset c b + c b = ∑ a ∈ insert b (earlierLabels b), c a := by
      rw [Finset.sum_insert hb]
      simp only [blockOffset, Nat.add_comm]
    _ ≤ ∑ a, c a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem blockOffset_add_le_of_lt (c : β → ℕ) {b d : β}
    (hbd : Fintype.equivFin β b < Fintype.equivFin β d) :
    blockOffset c b + c b ≤ blockOffset c d := by
  classical
  have hb : b ∉ earlierLabels b := by simp [earlierLabels]
  have hsub : insert b (earlierLabels b) ⊆ earlierLabels d := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa [earlierLabels] using hbd
    · have hab : Fintype.equivFin β a < Fintype.equivFin β b := by
        simpa [earlierLabels] using ha
      simpa [earlierLabels] using lt_trans hab hbd
  calc
    blockOffset c b + c b = ∑ a ∈ insert b (earlierLabels b), c a := by
      rw [Finset.sum_insert hb]
      simp only [blockOffset, Nat.add_comm]
    _ ≤ blockOffset c d := Finset.sum_le_sum_of_subset hsub

variable (A : β → Type uA) [∀ b, Fintype (A b)]

/-- The position of an element in the concatenation of the label fibres. -/
def groupedIndex (p : Σ b, A b) : Fin (∑ b, Fintype.card (A b)) :=
  ⟨blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val,
    lt_of_lt_of_le (Nat.add_lt_add_left (Fintype.equivFin (A p.1) p.2).isLt _)
      (blockOffset_add_le_total _ _)⟩

theorem groupedIndex_injective : Function.Injective (groupedIndex A) := by
  intro p q hpq
  have hv := congrArg Fin.val hpq
  change blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val =
    blockOffset (fun b => Fintype.card (A b)) q.1 +
      (Fintype.equivFin (A q.1) q.2).val at hv
  have he : p.1 = q.1 := by
    by_contra hne
    have hrne : Fintype.equivFin β p.1 ≠ Fintype.equivFin β q.1 :=
      fun h => hne ((Fintype.equivFin β).injective h)
    rcases lt_or_gt_of_ne hrne with hlt | hlt
    · have hoff := blockOffset_add_le_of_lt (fun b => Fintype.card (A b)) hlt
      have hp := (Fintype.equivFin (A p.1) p.2).isLt
      omega
    · have hoff := blockOffset_add_le_of_lt (fun b => Fintype.card (A b)) hlt
      have hq := (Fintype.equivFin (A q.1) q.2).isLt
      omega
  rcases p with ⟨b, x⟩
  rcases q with ⟨d, y⟩
  dsimp only at he hv
  subst d
  have hxy : x = y := (Fintype.equivFin (A b)).injective (Fin.ext (by omega))
  subst y
  rfl

/-- A bijective enumeration which keeps each label fibre contiguous. -/
def groupedEquiv : (Σ b, A b) ≃ Fin (∑ b, Fintype.card (A b)) :=
  Equiv.ofBijective (groupedIndex A)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨groupedIndex_injective A, by simp⟩)

theorem groupedEquiv_val (p : Σ b, A b) :
    (groupedEquiv A p).val = blockOffset (fun b => Fintype.card (A b)) p.1 +
      (Fintype.equivFin (A p.1) p.2).val := rfl

variable {α : Type uAlpha} [Fintype α] [DecidableEq β]

/-- Bounded label multiplicities admit a partition into equally populated
rows, with at most one occurrence of each label in each row. The cardinal
bound is the integer floor, so it applies also to empty rows and words. -/
theorem exists_balanced_rows (f : α → β) (w : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w) :
    ∃ row : α → Fin w,
      (∀ r, Set.InjOn f {a | row a = r}) ∧
      (∀ r, Fintype.card α / w ≤ Fintype.card {a : α // row a = r}) := by
  classical
  let B : β → Type _ := fun b => {a : α // f a = b}
  let n := ∑ b, Fintype.card (B b)
  let e : α ≃ Fin n := (Equiv.sigmaFiberEquiv f).symm.trans (groupedEquiv B)
  have hn : n = Fintype.card α := by
    calc
      n = Fintype.card (Σ b, B b) := by simp [n]
      _ = Fintype.card α := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  let row : α → Fin w := fun a => ⟨(e a).val % w, Nat.mod_lt _ hw⟩
  refine ⟨row, ?_, ?_⟩
  · intro r x hx y hy hlabel
    have hex : (e x).val = blockOffset (fun b => Fintype.card (B b)) (f x) +
        (Fintype.equivFin (B (f x)) ⟨x, rfl⟩).val := rfl
    have hey : (e y).val = blockOffset (fun b => Fintype.card (B b)) (f y) +
        (Fintype.equivFin (B (f y)) ⟨y, rfl⟩).val := rfl
    have hxp := (Fintype.equivFin (B (f x)) ⟨x, rfl⟩).isLt
    have hyp := (Fintype.equivFin (B (f y)) ⟨y, rfl⟩).isLt
    have hxm : Fintype.card (B (f x)) ≤ w := hm (f x)
    have hym : Fintype.card (B (f y)) ≤ w := hm (f y)
    have hoff : blockOffset (fun b => Fintype.card (B b)) (f x) =
        blockOffset (fun b => Fintype.card (B b)) (f y) := congrArg _ hlabel
    have hmod : (e x).val % w = (e y).val % w :=
      congrArg Fin.val (hx.trans hy.symm)
    apply e.injective
    apply Fin.ext
    exact eq_of_mod_eq_of_mem_interval
      (a := blockOffset (fun b => Fintype.card (B b)) (f x))
      (by omega) (by omega) (by omega) (by omega) hmod
  · intro r
    have hecard : Fintype.card {a : α // row a = r} =
        Fintype.card {i : Fin n // i.val % w = r.val} :=
      Fintype.card_congr (e.subtypeEquiv (fun a => by
        change (⟨(e a).val % w, Nat.mod_lt _ hw⟩ : Fin w) = r ↔ _
        exact Fin.ext_iff))
    rw [hecard, ← hn]
    exact card_mod_row_subtype_lower n w hw r

/-- Explicit finite-set form: the rows partition the positions. -/
theorem exists_balanced_row_finsets (f : α → β) (w : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w) :
    ∃ rows : Fin w → Finset α,
      (∀ a, ∃! r, a ∈ rows r) ∧
      (∀ r, Set.InjOn f (rows r)) ∧
      (∀ r, Fintype.card α / w ≤ (rows r).card) := by
  classical
  obtain ⟨row, hinj, hcard⟩ := exists_balanced_rows f w hw hm
  refine ⟨fun r => Finset.univ.filter fun a => row a = r, ?_, ?_, ?_⟩
  · intro a
    refine ⟨row a, by simp, ?_⟩
    intro r hr
    simpa using (Finset.mem_filter.mp hr).2.symm
  · intro r x hx y hy hxy
    exact hinj r (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  · intro r
    simpa only [Fintype.card_subtype] using hcard r

/-- Light positions in a word admit rows of size at least `M / 10`, once
their number is at least one tenth of `k` and every label has multiplicity at
most `w` with `M * w ≤ k`. -/
theorem exists_light_row_finsets (f : α → β) (M w k : ℕ) (hw : 0 < w)
    (hm : ∀ b, Fintype.card {a : α // f a = b} ≤ w)
    (hwidth : M * w ≤ k) (hlight : k ≤ 10 * Fintype.card α) :
    ∃ rows : Fin w → Finset α,
      (∀ a, ∃! r, a ∈ rows r) ∧
      (∀ r, Set.InjOn f (rows r)) ∧
      (∀ r, M / 10 ≤ (rows r).card) := by
  obtain ⟨rows, hpart, hinj, hcard⟩ := exists_balanced_row_finsets f w hw hm
  exact ⟨rows, hpart, hinj, fun r =>
    (div_ten_le_div_of_sandwich hw hwidth hlight).trans (hcard r)⟩

variable {ι : Type uIndex} [Fintype ι] [DecidableEq ι]

/-- Balance on each fibre of a row assignment implies balance on all positions.
The factor `q = 4` is the quarter-balance used in the outer coloring. -/
theorem row_balance_aggregate (row : α → ι) (p : α → Prop) [DecidablePred p]
    (q : ℕ)
    (hrow : ∀ r,
      (Finset.univ.filter (fun a => row a = r)).card ≤
        q * ((Finset.univ.filter (fun a => row a = r)).filter p).card) :
    Fintype.card α ≤ q * (Finset.univ.filter p).card := by
  classical
  have htotal :
      (∑ r : ι, (Finset.univ.filter (fun a : α => row a = r)).card) =
        Fintype.card α := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset ι) row
  have hselected :
      (∑ r : ι, ((Finset.univ.filter (fun a : α => row a = r)).filter p).card) =
        (Finset.univ.filter p).card := by
    simpa [Finset.filter_filter, and_comm] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter p) (Finset.univ : Finset ι) row
  calc
    Fintype.card α =
        ∑ r : ι, (Finset.univ.filter (fun a : α => row a = r)).card := htotal.symm
    _ ≤ ∑ r : ι,
        q * ((Finset.univ.filter (fun a : α => row a = r)).filter p).card :=
      Finset.sum_le_sum fun r _ => hrow r
    _ = q * (Finset.univ.filter p).card := by rw [← Finset.mul_sum, hselected]

/-- Explicit partition version of `row_balance_aggregate`. The only partition
hypothesis is unique membership; its disjointness and completeness are used. -/
theorem partition_balance_aggregate (rows : ι → Finset α)
    (hpart : ∀ a, ∃! r, a ∈ rows r) (p : α → Prop) [DecidablePred p]
    (q : ℕ) (hrow : ∀ r, (rows r).card ≤ q * ((rows r).filter p).card) :
    Fintype.card α ≤ q * (Finset.univ.filter p).card := by
  classical
  let row : α → ι := fun a => Classical.choose (hpart a).exists
  have hmem : ∀ a, a ∈ rows (row a) := fun a =>
    Classical.choose_spec (hpart a).exists
  have hfiber : ∀ r,
      Finset.univ.filter (fun a : α => row a = r) = rows r := by
    intro r
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      rw [← ha]
      exact hmem a
    · intro ha
      exact (hpart a).unique (hmem a) ha
  apply row_balance_aggregate row p q
  intro r
  simpa only [hfiber r] using hrow r

end

end QuantitativeVanDerWaerden

end OAI
