import OAI.NumberTheory.Ostmann.Characters.PolynomialSupportPartition

namespace OAI

noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Ostmann.Characters

abbrev CutPieceIndex (cuts : Finset ℝ) := CutCellIndex cuts ⊕ {x : ℝ // x ∈ cuts}

def cutPiece (cuts : Finset ℝ) : CutPieceIndex cuts → Set ℝ
  | Sum.inl a => cutCell cuts a
  | Sum.inr a => {(a : ℝ)}

theorem card_cutPieceIndex (cuts : Finset ℝ) :
    Fintype.card (CutPieceIndex cuts) = 2 * cuts.card + 1 := by
  simp only [CutPieceIndex, Fintype.card_sum, card_cutCellIndex, Fintype.card_coe]
  omega

theorem cutPiece_convex (cuts : Finset ℝ) (a : CutPieceIndex cuts) :
    Convex ℝ (cutPiece cuts a) := by
  cases a with
  | inl a => exact cutCell_convex cuts a
  | inr a => exact convex_singleton _

theorem iUnion_cutPiece (cuts : Finset ℝ) :
    (⋃ a : CutPieceIndex cuts, cutPiece cuts a) = Set.univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases hx : x ∈ cuts
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · obtain ⟨a, ha⟩ := exists_mem_cutCell cuts hx
    exact ⟨Sum.inl a, ha⟩

theorem cutPiece_pairwiseDisjoint (cuts : Finset ℝ) :
    Pairwise (fun a b : CutPieceIndex cuts => Disjoint (cutPiece cuts a) (cutPiece cuts b)) := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b => exact cutCell_pairwiseDisjoint cuts (fun h => hab (congrArg Sum.inl h))
      | inr b =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          have hxb : x = (b : ℝ) := hy
          exact cutCell_avoids cuts a hx (hxb.symm ▸ b.property)
  | inr a =>
      cases b with
      | inl b =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          have hxa : x = (a : ℝ) := hx
          exact cutCell_avoids cuts b hy (hxa.symm ▸ a.property)
      | inr b =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          have hxa : x = (a : ℝ) := hx
          have hxb : x = (b : ℝ) := hy
          apply hab
          exact congrArg Sum.inr (Subtype.ext (hxa.symm.trans hxb))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem polynomialSupport_boolean_on_piece (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (strict : ι → Bool) (a : CutPieceIndex (polynomialSupportCuts p q)) :
    ∃ b : Bool, ∀ x ∈ cutPiece (polynomialSupportCuts p q) a,
      polynomialSupport p strict x ↔ b = true := by
  classical
  cases a with
  | inl a => exact polynomialSupport_boolean_on_cell p q strict a
  | inr a =>
      refine ⟨decide (polynomialSupport p strict a), ?_⟩
      intro x hx
      have hxa : x = (a : ℝ) := hx
      simp [hxa]

theorem polynomialArgument_monotone_on_piece (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (d : κ → ℝ) (a : CutPieceIndex (polynomialSupportCuts p q)) (j : κ) :
    MonotoneOn (fun x => (q j).eval x / d j) (cutPiece (polynomialSupportCuts p q) a) ∨
      AntitoneOn (fun x => (q j).eval x / d j) (cutPiece (polynomialSupportCuts p q) a) := by
  cases a with
  | inl a => exact polynomialArgument_monotone_on_cell p q d a j
  | inr a =>
      left
      intro x hx y hy hxy
      have hxa : x = (a : ℝ) := hx
      have hya : y = (a : ℝ) := hy
      simp [hxa, hya]

theorem polynomial_support_total_partition (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (strict : ι → Bool) (d : κ → ℝ) :
    Fintype.card (CutPieceIndex (polynomialSupportCuts p q)) ≤
        2 * ((∑ i, (p i).natDegree) + ∑ j, ((q j).natDegree - 1)) + 1 ∧
    (⋃ a : CutPieceIndex (polynomialSupportCuts p q),
      cutPiece (polynomialSupportCuts p q) a) = Set.univ ∧
    Pairwise (fun a b : CutPieceIndex (polynomialSupportCuts p q) =>
      Disjoint (cutPiece (polynomialSupportCuts p q) a) (cutPiece (polynomialSupportCuts p q) b)) ∧
    ∀ a : CutPieceIndex (polynomialSupportCuts p q),
      Convex ℝ (cutPiece (polynomialSupportCuts p q) a) ∧
      (∃ b : Bool, ∀ x ∈ cutPiece (polynomialSupportCuts p q) a,
        polynomialSupport p strict x ↔ b = true) ∧
      ∀ j, MonotoneOn (fun x => (q j).eval x / d j) (cutPiece (polynomialSupportCuts p q) a) ∨
        AntitoneOn (fun x => (q j).eval x / d j) (cutPiece (polynomialSupportCuts p q) a) := by
  refine ⟨?_, iUnion_cutPiece _, cutPiece_pairwiseDisjoint _, ?_⟩
  · rw [card_cutPieceIndex]
    have h := polynomialSupportCuts_card_le p q
    omega
  · intro a
    exact ⟨cutPiece_convex _ a, polynomialSupport_boolean_on_piece p q strict a,
      polynomialArgument_monotone_on_piece p q d a⟩

end Ostmann.Characters

end

end OAI
