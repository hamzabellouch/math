import OAI.NumberTheory.DukePrimeDegree.Geometry.NextGroupConjugation

namespace OAI

/-! # Remaining-product constancy along the selected root -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_nextProduct_constancy (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d+1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ r : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct r) ∉ N →
        q.nextIntrinsicProduct d μ (rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct r)) =
          q.nextIntrinsicProduct d μ x := by
  have H (p : q.NextRoot) : ∃ N : Set (X (d+1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ r : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct r) ∉ N →
        intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ
          (rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct r)) =
        intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x := by
    have hf : ¬ (q.root.1 = p.val.1 ∧ q.root.2 = p.val.2) := by
      rintro ⟨h₁,h₂⟩
      exact (Finset.mem_erase.mp p.prop).1 (Prod.ext h₁.symm h₂.symm)
    have hb : ¬ (q.root.1 = p.val.2 ∧ q.root.2 = p.val.1) := by
      rintro ⟨h₁,h₂⟩
      have hp := q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2
      rw [←h₁,←h₂] at hp
      exact lt_asymm q.positive hp
    exact exists_nullset_nonparallel_root_constancy d
      (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) q.distinct hf hb μ hA
  choose N hN hN0 hconst using H
  refine ⟨⋃ p, N p,MeasurableSet.iUnion hN,measure_iUnion_null hN0,?_⟩
  intro x hx r hy
  have he : (fun p : q.NextRoot =>
      intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ
        (rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct r))) =
      (fun p : q.NextRoot =>
        intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x) := by
    funext p
    exact hconst p x (fun h => hx (mem_iUnion.mpr ⟨p,h⟩)) r
      (fun h => hy (mem_iUnion.mpr ⟨p,h⟩))
  unfold InitialRootStep.nextIntrinsicProduct
  rw [he]

end DukePrimeDegree

end

end OAI
