import Mathlib

namespace OAI

noncomputable section
open Set
namespace Ostmann.Characters

abbrev CutCellIndex (cuts : Finset ℝ) := Option {x : ℝ // x ∈ cuts}

def cutCell (cuts : Finset ℝ) : CutCellIndex cuts → Set ℝ
  | none => {x | ∀ b ∈ cuts, x < b}
  | some a => {x | (a : ℝ) < x ∧ ∀ b ∈ cuts, (a : ℝ) < b → x < b}

theorem card_cutCellIndex (cuts : Finset ℝ) :
    Fintype.card (CutCellIndex cuts) = cuts.card + 1 := by
  simp [CutCellIndex]

theorem cutCell_convex (cuts : Finset ℝ) (i : CutCellIndex cuts) :
    Convex ℝ (cutCell cuts i) := by
  apply convex_iff_ordConnected.mpr
  constructor
  intro a ha b hb x hx
  cases i with
  | none => exact fun c hc => hx.2.trans_lt (hb c hc)
  | some c => exact ⟨ha.1.trans_le hx.1, fun d hd hcd => hx.2.trans_lt (hb.2 d hd hcd)⟩

theorem cutCell_isOpen (cuts : Finset ℝ) (i : CutCellIndex cuts) :
    IsOpen (cutCell cuts i) := by
  cases i with
  | none =>
      change IsOpen {x : ℝ | ∀ b ∈ cuts, x < b}
      simp only [ofPred_forall]
      exact isOpen_biInter_finset fun b _ => isOpen_Iio
  | some a =>
      change IsOpen ({x : ℝ | (a : ℝ) < x} ∩ {x | ∀ b ∈ cuts, (a : ℝ) < b → x < b})
      apply isOpen_Ioi.inter
      simp only [ofPred_forall]
      apply isOpen_biInter_finset
      intro b hb
      by_cases hab : (a : ℝ) < b
      · simp only [hab, iInter_true]
        exact isOpen_lt continuous_id continuous_const
      · simp [hab]

theorem cutCell_avoids (cuts : Finset ℝ) (i : CutCellIndex cuts)
    {x : ℝ} (hx : x ∈ cutCell cuts i) : x ∉ cuts := by
  intro hcut
  cases i with
  | none => exact lt_irrefl x (hx x hcut)
  | some a => exact lt_irrefl x (hx.2 x hcut hx.1)

theorem exists_mem_cutCell (cuts : Finset ℝ) {x : ℝ} (hx : x ∉ cuts) :
    ∃ i : CutCellIndex cuts, x ∈ cutCell cuts i := by
  classical
  let lower := cuts.filter (fun a => a < x)
  have hlt {b : ℝ} (hb : b ∈ cuts) (hbx : b ≤ x) : b < x :=
    lt_of_le_of_ne hbx (fun heq => hx (heq ▸ hb))
  by_cases hn : lower.Nonempty
  · let a := lower.max' hn
    have ha : a ∈ lower := Finset.max'_mem lower hn
    have hacut : a ∈ cuts := (Finset.mem_filter.mp ha).1
    have hax : a < x := (Finset.mem_filter.mp ha).2
    refine ⟨some ⟨a, hacut⟩, hax, ?_⟩
    intro b hb hab
    by_contra h
    have hblow : b ∈ lower := Finset.mem_filter.mpr ⟨hb, hlt hb (le_of_not_gt h)⟩
    exact not_lt_of_ge (Finset.le_max' lower b hblow) hab
  · refine ⟨none, ?_⟩
    intro b hb
    by_contra h
    exact hn ⟨b, Finset.mem_filter.mpr ⟨hb, hlt hb (le_of_not_gt h)⟩⟩

theorem cutCell_pairwiseDisjoint (cuts : Finset ℝ) :
    Pairwise (fun i j : CutCellIndex cuts => Disjoint (cutCell cuts i) (cutCell cuts j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases i with
  | none =>
      cases j with
      | none => exact hij rfl
      | some b => exact (not_lt_of_ge (hx b b.property).le) hy.1
  | some a =>
      cases j with
      | none => exact (not_lt_of_ge (hy a a.property).le) hx.1
      | some b =>
          have hab : (a : ℝ) ≠ b := by
            intro heq
            apply hij
            exact congrArg some (Subtype.ext heq)
          rcases lt_or_gt_of_ne hab with hab | hba
          · exact (not_lt_of_ge (hx.2 b b.property hab).le) hy.1
          · exact (not_lt_of_ge (hy.2 a a.property hba).le) hx.1

theorem iUnion_cutCell (cuts : Finset ℝ) :
    (⋃ i : CutCellIndex cuts, cutCell cuts i) = (cuts : Set ℝ)ᶜ := by
  ext x
  simp only [mem_iUnion, mem_compl_iff, Finset.mem_coe]
  exact ⟨fun ⟨i, hi⟩ => cutCell_avoids cuts i hi, exists_mem_cutCell cuts⟩

end Ostmann.Characters

end

end OAI
