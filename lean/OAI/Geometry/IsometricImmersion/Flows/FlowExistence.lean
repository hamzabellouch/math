import OAI.Geometry.IsometricImmersion.Energy.WeightPrimitive
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem coordinatePoint_mem_modelSquare {t y : ℝ}
    (ht : t ∈ Icc (-3 : ℝ) 3) (hy : y ∈ Icc (-3 : ℝ) 3) :
    coordinatePoint t y ∈ modelSquare := by
  simp only [mem_Icc] at ht hy
  constructor <;> intro i <;> fin_cases i <;> simp [coordinatePoint] <;> tauto

def flowField (q : Coord → ℝ) (t y : ℝ) : ℝ := -q (coordinatePoint t y)

variable {q : Coord → ℝ} {U : Set Coord}

theorem flowField_hasDerivAt_y (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    {t y : ℝ} (hp : coordinatePoint t y ∈ U) :
    HasDerivAt (flowField q t) (-coordPartial 1 q (coordinatePoint t y)) y := by
  have hd := (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y t y)).neg

theorem exists_flowField_lipschitz (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc (-2 : ℝ) 2,
      LipschitzOnWith L (flowField q t) (closedBall (0 : ℝ) 3) := by
  have hc : ContinuousOn (coordPartial 1 q) modelSquare :=
    (partial_contDiffOn hq hU 1).continuousOn.mono hSU
  obtain ⟨M, hM⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hc
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨L, ?_⟩
  intro t ht
  have hmem (y : ℝ) (hy : y ∈ closedBall (0 : ℝ) 3) :
      coordinatePoint t y ∈ modelSquare := by
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hy
    exact coordinatePoint_mem_modelSquare ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
  apply (convex_closedBall (0 : ℝ) 3).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun y hy => (flowField_hasDerivAt_y hq hU (hSU (hmem y hy))).hasDerivWithinAt)
  intro y hy
  change ‖-coordPartial 1 q (coordinatePoint t y)‖ ≤ max M 0
  rw [norm_neg]
  exact (hM _ (hmem y hy)).trans (le_max_left _ _)

theorem exists_cap_picard (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ L : ℝ≥0, IsPicardLindelof (flowField q)
      (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2) 0 3 2 (1 / 100) L := by
  obtain ⟨L, hL⟩ := exists_flowField_lipschitz hq hU hSU
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    exact hq.continuousOn.neg.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => hSU (coordinatePoint_mem_modelSquare
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')))
  · intro t ht y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    have hm := coordinatePoint_mem_modelSquare (t := t) (y := y)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
    simpa only [flowField, norm_neg, Real.norm_eq_abs, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using hsmall _ hm
  · norm_num

theorem exists_cap_trajectory (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) :
    ∃ y : ℝ → ℝ, y 0 = s ∧ ContDiffOn ℝ ∞ y (Icc (-2 : ℝ) 2) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt y (-q (coordinatePoint t (y t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2, |y t - s| ≤ (1 : ℝ) / 100 * |t|) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2, |y t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2, y t ∈ closedBall (0 : ℝ) 3) := by
  obtain ⟨L, hPL⟩ := exists_cap_picard hq hU hSU hsmall
  have hsball : s ∈ closedBall (0 : ℝ) (↑(2 : ℝ≥0)) := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, NNReal.coe_ofNat] using abs_le.mpr hs
  have hz : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by norm_num
  obtain ⟨alpha, halpha⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hsball
  have hinit : alpha.compProj 0 = s := by
    rw [ODE.FunSpace.compProj_of_mem hz, ← halpha]
    exact ODE.FunSpace.next_apply₀ hPL hsball alpha
  have hderiv (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) :
      HasDerivWithinAt alpha.compProj (flowField q t (alpha.compProj t))
        (Icc (-2 : ℝ) 2) t := by
    apply ODE.hasDerivWithinAt_picard_Icc (show (0 : ℝ) ∈ Icc (-2 : ℝ) 2 by norm_num)
      hPL.continuousOn_uncurry alpha.continuous_compProj.continuousOn
      (fun _ _ => alpha.compProj_mem_closedBall hPL.mul_max_le) s ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← halpha]
    rw [ODE.FunSpace.compProj_of_mem ht']
    exact ODE.FunSpace.next_apply hPL hsball alpha (t := ⟨t', ht'⟩)
  have hrange (t : ℝ) : alpha.compProj t ∈ closedBall (0 : ℝ) 3 :=
    alpha.compProj_mem_closedBall hPL.mul_max_le
  have hdispl (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) :
      |alpha.compProj t - s| ≤ (1 : ℝ) / 100 * |t| := by
    have hh := alpha.lipschitzWith.dist_le_mul ⟨t, ht⟩
      (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2)
    have ha0 : alpha ⟨0, hz⟩ = s := by
      simpa only [ODE.FunSpace.compProj_of_mem hz] using hinit
    rw [← ODE.FunSpace.compProj_of_mem ht, ha0] at hh
    simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using hh
  have hfield : ContDiffOn ℝ ∞ (uncurry (flowField q))
      (Icc (-2 : ℝ) 2 ×ˢ closedBall (0 : ℝ) 3) := by
    apply hq.neg.comp (by unfold coordinatePoint; fun_prop)
    intro p hp
    have hy' : |p.2| ≤ 3 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hp.2
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩ (abs_le.mp hy'))
  refine ⟨alpha.compProj, hinit,
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield hderiv (fun t _ => hrange t),
    hderiv, hdispl, ?_, fun t _ => hrange t⟩
  intro t ht
  have hdt := hdispl t ht
  have ht2 := abs_le.mpr ht
  nlinarith

end SmoothLocal.Flow

end

end OAI
