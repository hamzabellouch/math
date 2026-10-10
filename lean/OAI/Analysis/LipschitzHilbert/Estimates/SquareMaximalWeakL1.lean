import OAI.Analysis.LipschitzHilbert.Estimates.DyadicSquareWeakL1

namespace OAI

/-! A weak L1 square maximal majorant using nine fixed grid pairs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

def squareSup (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z)

theorem squareSup_measurable (f : ℝ × ℝ → ℝ≥0∞) : Measurable (squareSup f) := by
  have h (s : Finset (GridChoice × GridChoice)) : Measurable (fun z =>
      s.sup (fun q => gridSquareSup q.1.val q.2.val f z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih => simpa only [Finset.sup_insert] using (gridSquareSup_measurable q.1.val q.2.val f).max ih
  exact h Finset.univ

theorem gridSquareSup_le_squareSup (q : GridChoice × GridChoice)
    (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) :
    gridSquareSup q.1.val q.2.val f z ≤ squareSup f z :=
  Finset.le_sup (f := fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z) (Finset.mem_univ q)

theorem squareSup_weak_L1 (f : ℝ × ℝ → ℝ≥0∞) (t : ℝ≥0∞)
    (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < squareSup f z} ≤
      9 * t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  have hsub : {z | t < squareSup f z} ⊆
      ⋃ q : GridChoice × GridChoice, {z | t < gridSquareSup q.1.val q.2.val f z} := by
    intro z hz
    change t < Finset.univ.sup (fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z) at hz
    obtain ⟨q,_,hq⟩ := Finset.lt_sup_iff.mp hz
    exact mem_iUnion.mpr ⟨q,hq⟩
  calc
    _ ≤ (volume.prod volume) (⋃ q : GridChoice × GridChoice,
        {z | t < gridSquareSup q.1.val q.2.val f z}) := measure_mono hsub
    _ ≤ ∑ q : GridChoice × GridChoice,
        (volume.prod volume) {z | t < gridSquareSup q.1.val q.2.val f z} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : GridChoice × GridChoice, t⁻¹ * ∫⁻ z, f z ∂volume.prod volume :=
      Finset.sum_le_sum (fun q _ => gridSquareSup_weak_L1 q.1.val q.2.val f t ht htop)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,gridChoice_card,nsmul_eq_mul]
      norm_num
      rw [mul_assoc]

def centeredSquare (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  Icc (c.1-r) (c.1+r) ×ˢ Icc (c.2-r) (c.2+r)

theorem centeredSquare_measurable (c : ℝ × ℝ) (r : ℝ) : MeasurableSet (centeredSquare c r) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem centeredSquare_volume (c : ℝ × ℝ) (r : ℝ) :
    (volume.prod volume) (centeredSquare c r) = ENNReal.ofReal (2*r) * ENNReal.ofReal (2*r) := by
  rw [centeredSquare,Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  congr 2 <;> ring

theorem square_integral_le_squareSup (f : ℝ × ℝ → ℝ≥0∞) (c : ℝ × ℝ)
    (r : ℝ) (hr : 0 < r) {z : ℝ × ℝ} (hz : z ∈ centeredSquare c r) :
    (∫⁻ w in centeredSquare c r, f w ∂volume.prod volume) ≤
      36 * (volume.prod volume) (centeredSquare c r) * squareSup f z := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0 < 12*r by positivity) (by norm_num : (1:ℝ) < 2)
  change scale k ≤ 12*r at hlo
  change 12*r < scale (k+1) at hhi
  rw [scale_succ] at hhi
  have hsmall : 6*r < scale k := by linarith
  obtain ⟨qx,hqx,i,hx⟩ := exists_three_grid_cover k c.1 r hr.le hsmall
  obtain ⟨qy,hqy,j,hy⟩ := exists_three_grid_cover k c.2 r hr.le hsmall
  let p : SquareIndex := (k,i,j)
  let q : GridChoice × GridChoice := (⟨qx,hqx⟩,⟨qy,hqy⟩)
  have hsub : centeredSquare c r ⊆ squareCell qx qy p := Set.prod_mono hx hy
  have hvolpos : (volume.prod volume) (squareCell qx qy p) ≠ 0 := by
    rw [squareCell_volume]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (scale_pos k)))
  have hvolfinite : (volume.prod volume) (squareCell qx qy p) ≠ ∞ := by
    rw [squareCell_volume]
    exact ENNReal.ofReal_ne_top
  have hmean := (square_average_le_gridSquareSup qx qy f p (hsub hz)).trans
    (gridSquareSup_le_squareSup q f z)
  have hvol : (volume.prod volume) (squareCell qx qy p) ≤
      36 * (volume.prod volume) (centeredSquare c r) := by
    rw [squareCell_volume,centeredSquare_volume,←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]
    rw [show (36:ℝ≥0∞) = ENNReal.ofReal 36 by norm_num,
      ←ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    change (scale k)^2 ≤ 36*((2*r)*(2*r))
    nlinarith [scale_pos k]
  calc
    _ ≤ ∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume := lintegral_mono_set hsub
    _ = (volume.prod volume) (squareCell qx qy p) *
        ((∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) := by
      rw [mul_comm,ENNReal.div_mul_cancel hvolpos hvolfinite]
    _ ≤ _ := mul_le_mul' hvol hmean

end LipschitzHilbert.DyadicLineGrid

end

end OAI
