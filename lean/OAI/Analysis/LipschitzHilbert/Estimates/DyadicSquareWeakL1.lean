import OAI.Analysis.LipschitzHilbert.Estimates.LaminarWeakL1
import OAI.Analysis.LipschitzHilbert.Geometry.SourceThreeGridCover
import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal

namespace OAI

/-! All-scale square averages in a fixed pair of dyadic grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev SquareIndex := ℤ × ℤ × ℤ

def squareCell (qx qy : ℤ) (p : SquareIndex) : Set (ℝ × ℝ) :=
  cell qx p.1 p.2.1 ×ˢ cell qy p.1 p.2.2

theorem squareCell_measurable (qx qy : ℤ) (p : SquareIndex) :
    MeasurableSet (squareCell qx qy p) :=
  (cell_measurable _ _ _).prod (cell_measurable _ _ _)

theorem cell_volume (q k j : ℤ) : volume (cell q k j) = ENNReal.ofReal (scale k) := by
  rw [←cell_length q k j]
  exact (ENNReal.ofReal_toReal measure_Ico_lt_top.ne).symm

theorem squareCell_volume (qx qy : ℤ) (p : SquareIndex) :
    (volume.prod volume) (squareCell qx qy p) = ENNReal.ofReal ((scale p.1)^2) := by
  rw [squareCell,Measure.prod_prod,cell_volume,cell_volume,←ENNReal.ofReal_mul (scale_pos _).le]
  congr 1
  ring

theorem squareCell_ranked (qx qy : ℤ) (p q : SquareIndex) (h : q.1 ≤ p.1)
    (hint : (squareCell qx qy p ∩ squareCell qx qy q).Nonempty) :
    squareCell qx qy q ⊆ squareCell qx qy p := by
  obtain ⟨z,hz1,hz2⟩ := hint
  exact Set.prod_mono
    (cell_subset_of_intersect h ⟨z.1,hz2.1,hz1.1⟩)
    (cell_subset_of_intersect h ⟨z.2,hz2.2,hz1.2⟩)

def gridSquareSup (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ⨆ p : SquareIndex, (squareCell qx qy p).indicator
    (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
      (volume.prod volume) (squareCell qx qy p)) z

theorem gridSquareSup_measurable (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞) :
    Measurable (gridSquareSup qx qy f) :=
  Measurable.iSup (fun p => measurable_const.indicator (squareCell_measurable qx qy p))

theorem square_average_le_gridSquareSup (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞)
    (p : SquareIndex) {z : ℝ × ℝ} (hz : z ∈ squareCell qx qy p) :
    (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
      (volume.prod volume) (squareCell qx qy p) ≤ gridSquareSup qx qy f z := by
  calc
    _ = (squareCell qx qy p).indicator (fun _ =>
        (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z := (indicator_of_mem hz _).symm
    _ ≤ _ := le_iSup (fun p : SquareIndex => (squareCell qx qy p).indicator
      (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z) p

theorem gridSquareSup_weak_L1 (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < gridSquareSup qx qy f z} ≤
      t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  let G := {p : SquareIndex | t * (volume.prod volume) (squareCell qx qy p) ≤
    ∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume}
  have hsub : {z | t < gridSquareSup qx qy f z} ⊆ ⋃ p : G, squareCell qx qy p.val := by
    intro z hz
    change t < ⨆ p : SquareIndex, (squareCell qx qy p).indicator
      (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z at hz
    obtain ⟨p,hp⟩ := lt_iSup_iff.mp hz
    have hzp : z ∈ squareCell qx qy p := by
      by_contra hn
      simp only [indicator_of_notMem hn, not_lt_zero] at hp
    rw [indicator_of_mem hzp] at hp
    have hpos : (volume.prod volume) (squareCell qx qy p) ≠ 0 := by
      rw [squareCell_volume]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (scale_pos _)))
    have hfinite : (volume.prod volume) (squareCell qx qy p) ≠ ∞ := by
      rw [squareCell_volume]
      exact ENNReal.ofReal_ne_top
    have hg : p ∈ G := by
      change t * (volume.prod volume) (squareCell qx qy p) ≤ _
      calc
        _ ≤ ((∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
            (volume.prod volume) (squareCell qx qy p)) *
            (volume.prod volume) (squareCell qx qy p) := mul_le_mul' hp.le le_rfl
        _ = _ := ENNReal.div_mul_cancel hpos hfinite
    exact mem_iUnion.mpr ⟨⟨p,hg⟩,hzp⟩
  have hmass := ranked_countable_weak_bound (volume.prod volume)
    (fun p : G => squareCell qx qy p.val) (fun p => p.val.1)
    (fun p => squareCell_measurable qx qy p.val)
    (fun p q => squareCell_ranked qx qy p.val q.val) f t (fun p => p.property)
  calc
    _ ≤ (volume.prod volume) (⋃ p : G, squareCell qx qy p.val) := measure_mono hsub
    _ = t⁻¹ * (t * (volume.prod volume) (⋃ p : G, squareCell qx qy p.val)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel ht htop,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hmass

end LipschitzHilbert.DyadicLineGrid

end

end OAI
