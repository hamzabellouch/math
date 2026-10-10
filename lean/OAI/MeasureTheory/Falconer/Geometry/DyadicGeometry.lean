import OAI.MeasureTheory.Falconer.DistanceSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OAI

namespace PlanarFalconer
open Set Metric

structure DyadicSquare where
  x : ℝ
  y : ℝ
  side : ℝ

def DyadicSquare.carrier (Q : DyadicSquare) : Set Plane :=
  {z | Q.x ≤ z 0 ∧ z 0 < Q.x + Q.side ∧
       Q.y ≤ z 1 ∧ z 1 < Q.y + Q.side}

noncomputable def DyadicSquare.child (Q : DyadicSquare) (i j : Bool) : DyadicSquare :=
  ⟨Q.x + (if i then Q.side / 2 else 0),
   Q.y + (if j then Q.side / 2 else 0), Q.side / 2⟩

theorem DyadicSquare.child_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (i j : Bool) : 0 < (Q.child i j).side := by
  dsimp [child]
  positivity

theorem DyadicSquare.measurable (Q : DyadicSquare) : MeasurableSet Q.carrier := by
  have h0 : Continuous (fun z : Plane => z 0) := (EuclideanSpace.proj 0).continuous
  have h1 : Continuous (fun z : Plane => z 1) := (EuclideanSpace.proj 1).continuous
  exact (isClosed_le continuous_const h0).measurableSet.inter
    ((isOpen_lt h0 continuous_const).measurableSet.inter
    ((isClosed_le continuous_const h1).measurableSet.inter
    (isOpen_lt h1 continuous_const).measurableSet))

theorem DyadicSquare.child_subset (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    (i j : Bool) : (Q.child i j).carrier ⊆ Q.carrier := by
  have halfSide_nonneg : 0 ≤ Q.side / 2 := div_nonneg hQ (by norm_num)
  intro z hz
  cases i <;> cases j <;>
    simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
      add_zero, mem_ofPred_eq] at * <;>
    refine ⟨by linarith [halfSide_nonneg], by linarith [halfSide_nonneg],
      by linarith [halfSide_nonneg], by linarith [halfSide_nonneg]⟩

theorem DyadicSquare.cover_children (Q : DyadicSquare) :
    Q.carrier = ((Q.child false false).carrier ∪ (Q.child false true).carrier) ∪
      ((Q.child true false).carrier ∪ (Q.child true true).carrier) := by
  ext z
  simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
    add_zero, mem_ofPred_eq, mem_union]
  constructor
  · intro hz
    by_cases hx : z 0 < Q.x + Q.side / 2 <;>
      by_cases hy : z 1 < Q.y + Q.side / 2
    · exact Or.inl (Or.inl ⟨hz.1,hx,hz.2.2.1,hy⟩)
    · exact Or.inl (Or.inr ⟨hz.1,hx,by linarith,by linarith [hz.2.2.2]⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith [hz.2.1],hz.2.2.1,hy⟩)
    · exact Or.inr (Or.inr ⟨by linarith,by linarith [hz.2.1],
        by linarith,by linarith [hz.2.2.2]⟩)
  · intro hz
    rcases hz with (hz | hz) | (hz | hz) <;>
      refine ⟨by linarith [hz.1,hz.2.1], by linarith [hz.1,hz.2.1],
        by linarith [hz.2.2.1,hz.2.2.2], by linarith [hz.2.2.1,hz.2.2.2]⟩

theorem DyadicSquare.children_disjoint (Q : DyadicSquare)
    {i j i' j' : Bool} (h : (i,j) ≠ (i',j')) :
    Disjoint (Q.child i j).carrier (Q.child i' j').carrier := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  cases i <;> cases j <;> cases i' <;> cases j' <;>
    simp_all only [carrier, child, Bool.false_eq_true, ↓reduceIte,
      add_zero, mem_ofPred_eq, ne_eq, not_true_eq_false] <;> linarith

theorem DyadicSquare.dist_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    {z w : Plane} (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) :
    dist z w ≤ 2 * Q.side := by
  have h0 : |z 0 - w 0| ≤ Q.side := by
    apply abs_le.mpr; constructor <;> linarith [hz.1,hz.2.1,hw.1,hw.2.1]
  have h1 : |z 1 - w 1| ≤ Q.side := by
    apply abs_le.mpr; constructor <;>
      linarith [hz.2.2.1,hz.2.2.2,hw.2.2.1,hw.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq z w
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [dist_nonneg (x := z) (y := w)]

theorem DyadicSquare.ediam_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side) :
    ediam Q.carrier ≤ ENNReal.ofReal (2 * Q.side) := by
  apply Metric.ediam_le
  intro z hz w hw
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (Q.dist_le hQ hz hw)

end PlanarFalconer

end OAI
