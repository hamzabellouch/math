import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCellDensity
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxReproduction
import OAI.Analysis.LipschitzHilbert.Geometry.SourceWhitneyPacking

namespace OAI

/-! A disjoint half-open partition underneath the manuscript's closed
transverse cells. Boundary points are retained exactly once. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

def transverseCell (b W : ℝ) (n : ℤ) : Set ℝ :=
  Ico (b+(n:ℝ)*W-W/2) (b+(n:ℝ)*W+W/2)

theorem transverseCell_measurable (b W : ℝ) (n : ℤ) :
    MeasurableSet (transverseCell b W n) := measurableSet_Ico

theorem transverseCell_length (b W : ℝ) (n : ℤ) (hW : 0<W) :
    volume.real (transverseCell b W n)=W := by
  rw [transverseCell,Real.volume_real_Ico_of_le (by linarith)]
  ring

theorem transverseCell_bound (b W : ℝ) (n : ℤ) {y : ℝ}
    (hy : y∈transverseCell b W n) : |y-b-(n:ℝ)*W|≤W/2 := by
  exact abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

theorem transverseCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (Disjoint on transverseCell b W) := by
  have haux (n m : ℤ) (hlt : n<m) :
      Disjoint (transverseCell b W n) (transverseCell b W m) := by
    have hstep : (n:ℝ)+1≤m := by exact_mod_cast (show n+1≤m by omega)
    have hmul := mul_le_mul_of_nonneg_right hstep hW.le
    apply Set.disjoint_left.mpr
    intro y hyn hym
    have hny := hyn.2
    have hmy := hym.1
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact haux n m hlt
  · exact (haux m n hlt).symm

theorem mem_transverseCell_floor (b W y : ℝ) (hW : 0<W) :
    y∈transverseCell b W ⌊(y-b)/W+1/2⌋ := by
  have hl := Int.floor_le ((y-b)/W+1/2)
  have hu := Int.lt_floor_add_one ((y-b)/W+1/2)
  have hl' := mul_le_mul_of_nonneg_right hl hW.le
  have hu' := mul_lt_mul_of_pos_right hu hW
  have hc : ((y-b)/W+1/2)*W=y-b+W/2 := by field_simp
  rw [hc] at hl' hu'
  constructor <;> linarith

def partitionCell (b W : ℝ) (p : (ℤ×ℤ)×ℤ) : Set (ℝ×ℝ) :=
  cell 0 p.1.1 p.1.2 ×ˢ transverseCell b W p.2

theorem partitionCell_measurable (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    MeasurableSet (partitionCell b W p) :=
  (cell_measurable 0 p.1.1 p.1.2).prod (transverseCell_measurable b W p.2)

theorem partitionCell_finite (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    (volume.prod volume) (partitionCell b W p)≠∞ := by
  rw [partitionCell,Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ico_lt_top.ne measure_Ico_lt_top.ne

theorem partitionCell_area (b W : ℝ) (p : (ℤ×ℤ)×ℤ) (hW : 0<W) :
    (volume.prod volume).real (partitionCell b W p)=scale p.1.1*W := by
  rw [partitionCell,measureReal_prod_prod,cell_length,transverseCell_length b W p.2 hW]

theorem partitionCell_subset_box (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    partitionCell b W p⊆coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*W)
      (scale p.1.1/2) (W/2) := by
  intro z hz
  refine ⟨point_center_bound p.1.1 p.1.2 hz.1,?_⟩
  have h := transverseCell_bound b W p.2 hz.2
  simpa only [sub_add_eq_sub_sub] using h

theorem partitionCell_subset_treeCell (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    partitionCell b W p⊆treeCell 0 b W p.1.1 p.1.2 p.2 := by
  intro z hz
  refine ⟨hz.1,?_⟩
  simpa only [zero_mul,sub_zero] using transverseCell_bound b W p.2 hz.2

theorem partitionCell_disjoint {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (b W : ℝ) (hW : 0<W) (S : Set ((ℤ×ℤ)×ℤ))
    (hS : ∀ p∈S, Whitney tiles x ell p.1.1 p.1.2) :
    Set.Pairwise S (Disjoint on partitionCell b W) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro z hzp hzq
  by_cases he : p.1=q.1
  · have hn : p.2≠q.2 := by
      intro hn
      exact hpq (Prod.ext he hn)
    exact Set.disjoint_left.mp (transverseCell_disjoint b W hW hn) hzp.2 hzq.2
  · exact Set.disjoint_left.mp (whitney_disjoint tiles x ell (hS p hp) (hS q hq) he) hzp.1 hzq.1

end LipschitzHilbert.SourceWhitney

end

end OAI
