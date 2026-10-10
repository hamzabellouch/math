import OAI.NumberTheory.Ostmann.Characters.PolynomialSupportPartitionCells
import OAI.NumberTheory.Ostmann.Characters.PolynomialSupportPartitionSigns

namespace OAI

noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Ostmann.Characters
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def polynomialSupportCuts (p : ι → ℝ[X]) (q : κ → ℝ[X]) : Finset ℝ := by
  classical
  exact (Finset.univ.biUnion fun i => (p i).roots.toFinset) ∪
    (Finset.univ.biUnion fun j => (q j).derivative.roots.toFinset)

theorem support_roots_subset_cuts (p : ι → ℝ[X]) (q : κ → ℝ[X]) (i : ι) :
    (p i).roots.toFinset ⊆ polynomialSupportCuts p q := by
  classical
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

theorem critical_roots_subset_cuts (p : ι → ℝ[X]) (q : κ → ℝ[X]) (j : κ) :
    (q j).derivative.roots.toFinset ⊆ polynomialSupportCuts p q := by
  classical
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)

theorem polynomialSupportCuts_card_le (p : ι → ℝ[X]) (q : κ → ℝ[X]) :
    (polynomialSupportCuts p q).card ≤
      (∑ i, (p i).natDegree) + ∑ j, ((q j).natDegree - 1) := by
  classical
  unfold polynomialSupportCuts
  apply (Finset.card_union_le _ _).trans
  apply add_le_add
  · apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i hi
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  · apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro j hj
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (Polynomial.natDegree_derivative_le _))

theorem polynomialSupportCells_card_le (p : ι → ℝ[X]) (q : κ → ℝ[X]) :
    Fintype.card (CutCellIndex (polynomialSupportCuts p q)) ≤
      (∑ i, (p i).natDegree) + (∑ j, ((q j).natDegree - 1)) + 1 := by
  rw [card_cutCellIndex]
  exact Nat.add_le_add_right (polynomialSupportCuts_card_le p q) 1

def polynomialSupport (p : ι → ℝ[X]) (strict : ι → Bool) (x : ℝ) : Prop :=
  ∀ i, if strict i then (p i).eval x < 0 else (p i).eval x ≤ 0

theorem polynomialSupport_constant_on_cell (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (strict : ι → Bool) (a : CutCellIndex (polynomialSupportCuts p q))
    {x y : ℝ} (hx : x ∈ cutCell (polynomialSupportCuts p q) a)
    (hy : y ∈ cutCell (polynomialSupportCuts p q) a) :
    polynomialSupport p strict x ↔ polynomialSupport p strict y := by
  unfold polynomialSupport
  apply forall_congr'
  intro i
  have h := polynomial_relations_constant_on (p i)
    (cutCell_convex (polynomialSupportCuts p q) a).isPreconnected
    (fun t ht hr => cutCell_avoids _ a ht (support_roots_subset_cuts p q i hr)) hx hy
  cases strict i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact h.1
  · exact h.2.1

theorem polynomialSupport_boolean_on_cell (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (strict : ι → Bool) (a : CutCellIndex (polynomialSupportCuts p q)) :
    ∃ b : Bool, ∀ x ∈ cutCell (polynomialSupportCuts p q) a,
      polynomialSupport p strict x ↔ b = true := by
  classical
  by_cases h : ∃ y ∈ cutCell (polynomialSupportCuts p q) a, polynomialSupport p strict y
  · obtain ⟨y, hy, hs⟩ := h
    refine ⟨true, ?_⟩
    intro x hx
    have hx' := (polynomialSupport_constant_on_cell p q strict a hx hy).mpr hs
    simp [hx']
  · refine ⟨false, ?_⟩
    intro x hx
    have hx' : ¬ polynomialSupport p strict x := fun hs => h ⟨x, hx, hs⟩
    simp [hx']

theorem polynomialArgument_monotone_on_cell (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (d : κ → ℝ) (a : CutCellIndex (polynomialSupportCuts p q)) (j : κ) :
    MonotoneOn (fun x => (q j).eval x / d j) (cutCell (polynomialSupportCuts p q) a) ∨
      AntitoneOn (fun x => (q j).eval x / d j) (cutCell (polynomialSupportCuts p q) a) :=
  polynomial_div_const_monotone_or_antitone_on (q j) (d j)
    (cutCell_convex _ a)
    (fun _x hx hr => cutCell_avoids _ a hx (critical_roots_subset_cuts p q j hr))

theorem polynomial_support_partition (p : ι → ℝ[X]) (q : κ → ℝ[X])
    (strict : ι → Bool) (d : κ → ℝ) :
    ∃ cuts : Finset ℝ,
      cuts.card ≤ (∑ i, (p i).natDegree) + ∑ j, ((q j).natDegree - 1) ∧
      (⋃ a : CutCellIndex cuts, cutCell cuts a) = (cuts : Set ℝ)ᶜ ∧
      Pairwise (fun a b : CutCellIndex cuts => Disjoint (cutCell cuts a) (cutCell cuts b)) ∧
      ∀ a : CutCellIndex cuts,
        IsOpen (cutCell cuts a) ∧ Convex ℝ (cutCell cuts a) ∧
        (∃ b : Bool, ∀ x ∈ cutCell cuts a, polynomialSupport p strict x ↔ b = true) ∧
        ∀ j, MonotoneOn (fun x => (q j).eval x / d j) (cutCell cuts a) ∨
          AntitoneOn (fun x => (q j).eval x / d j) (cutCell cuts a) := by
  refine ⟨polynomialSupportCuts p q, polynomialSupportCuts_card_le p q,
    iUnion_cutCell _, cutCell_pairwiseDisjoint _, ?_⟩
  intro a
  exact ⟨cutCell_isOpen _ a, cutCell_convex _ a,
    polynomialSupport_boolean_on_cell p q strict a, polynomialArgument_monotone_on_cell p q d a⟩

end Ostmann.Characters

end

end OAI
