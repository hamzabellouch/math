import OAI.Analysis.LipschitzHilbert.Geometry.SelectedCountingEnergy
import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiCoveringReduction

namespace OAI

/-! The finite-family weak-(2,2) Lipschitz Kakeya estimate of Lacey--Li,
Memoirs AMS 205 (2010), no.965, result 1.10 / equation (1.11).
The proof uses the actual maximal-removal selection, the near/far overlap
bounds, and the proved weak-L1 auxiliary operators. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem laceyLiInput_proved : LaceyLiInput := by
  obtain ⟨m,D,hD⟩ := Rectangle.exists_finite_transverse_directions
  let B : ℝ≥0∞ := 1+(9+3*(m:ℝ≥0∞))*selectionThreshold⁻¹*ENNReal.ofReal (selectionDilation^2)
  have hη0 : selectionThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
  have hηtop : selectionThreshold ≠ ∞ := ENNReal.ofReal_ne_top
  have hBtop : B ≠ ∞ := by
    dsimp [B]
    exact ENNReal.add_ne_top.mpr ⟨by simp,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.add_ne_top.mpr ⟨by norm_num,ENNReal.mul_ne_top (by norm_num) (by simp)⟩)
        (ENNReal.inv_ne_top.mpr hη0))
        ENNReal.ofReal_ne_top⟩
  have hBCtop : B*1923 ≠ ∞ := ENNReal.mul_ne_top hBtop (by norm_num)
  let C : ℝ≥0 := max 1 (B*1923).toNNReal
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hBC : B*1923 ≤ (C:ℝ≥0∞) := by
    rw [←ENNReal.coe_toNNReal hBCtop]
    exact_mod_cast (le_max_right (1:ℝ≥0) (B*1923).toNNReal)
  have hCsq : B*1923 ≤ (C:ℝ≥0∞)^2 := by
    refine hBC.trans ?_
    have h1 : (1:ℝ≥0∞) ≤ C := by exact_mod_cast hC1
    simpa only [one_mul,pow_two] using mul_le_mul' h1 (le_refl (C:ℝ≥0∞))
  refine ⟨C,hCpos,?_⟩
  intro v K δ hv hu hδ hδ1 n R hR h hh t ht
  let stock : Finset (Fin n) := Finset.univ.filter (fun i => (t:ℝ≥0∞) < (R i).average h)
  obtain ⟨selected,hrun⟩ := rectangle_cover_run_maximal_exists
    (fun i => (D i).orthogonalCoordinates) R selectionDilation (by norm_num) selectionThreshold stock
  have henergy := selected_counting_energy D hD R stock selected hrun hv hu hδ hδ1
    (fun i _ => hR i)
  have hδ0 : (δ:ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  have hoverlap : (∫⁻ x, (rectangleCount R selected.toFinset x)^2) ≤
      (1923/(δ:ℝ≥0∞))*(∑ i ∈ selected.toFinset, volume (R i).carrier) := by
    calc
      _ = (δ:ℝ≥0∞)⁻¹*((δ:ℝ≥0∞)*(∫⁻ x, (rectangleCount R selected.toFinset x)^2)) := by
        rw [←mul_assoc,ENNReal.inv_mul_cancel hδ0 ENNReal.coe_ne_top,one_mul]
      _ ≤ (δ:ℝ≥0∞)⁻¹*(1923*(∑ i ∈ selected.toFinset, volume (R i).carrier)) :=
        mul_le_mul' le_rfl henergy
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hcover := maximal_selection_cover_bound (fun i => (D i).orthogonalCoordinates)
    (fun i => (D i).orthogonalCoordinates_measurePreserving) R selectionDilation (by norm_num)
    selectionThreshold hη0 hηtop stock selected hrun
  have hlevel : {x | (t:ℝ≥0∞) < rectangleMaximum R h x} ⊆ ⋃ i ∈ stock, (R i).carrier := by
    intro x hx
    change (t:ℝ≥0∞) < Finset.univ.sup (fun i => if x ∈ (R i).carrier then (R i).average h else 0) at hx
    obtain ⟨i,_,hi⟩ := Finset.lt_sup_iff.mp hx
    by_cases hxi : x ∈ (R i).carrier
    · rw [ite_eq_left hxi] at hi
      exact mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩,hxi⟩
    · rw [ite_eq_right hxi] at hi
      exact (not_lt_zero hi).elim
  have hcover' : volume {x | (t:ℝ≥0∞) < rectangleMaximum R h x} ≤
      B*(∑ i ∈ selected.toFinset, volume (R i).carrier) := by
    refine (measure_mono hlevel).trans ?_
    simpa only [Fintype.card_fin] using hcover
  have hhigh : ∀ i ∈ selected.toFinset, (t:ℝ≥0∞) ≤ (R i).average h := by
    intro i hi
    have his := hrun.selected_subset i (List.mem_toFinset.mp hi)
    exact (Finset.mem_filter.mp his).2.le
  have hweak := covering_weak_bound R selected.toFinset
    {x | (t:ℝ≥0∞) < rectangleMaximum R h x} h hh.aestronglyMeasurable
    (t:ℝ≥0∞) B (1923/(δ:ℝ≥0∞)) hhigh hcover' hoverlap
  refine hweak.trans (mul_le_mul' ?_ le_rfl)
  calc
    B*(1923/(δ:ℝ≥0∞)) = (B*1923)*(δ:ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ (C:ℝ≥0∞)^2*(δ:ℝ≥0∞)⁻¹ := mul_le_mul' hCsq le_rfl
    _ = _ := rfl

end LipschitzHilbert

end

end OAI
