import OAI.Analysis.CircleDomains.Probability.PathLengthMeasure
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! A Lipschitz parameterization has arclength measure dominated by
its Lipschitz constant times one-dimensional Hausdorff measure on time. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

theorem variation_time_identity {a b : PathTime} (hab : a ≤ b) :
    eVariationOn (id : PathTime → PathTime) (Icc a b) = edist b a := by
  have hm : Monotone (Subtype.val : PathTime → ℝ) := fun _ _ h => h
  have he : eVariationOn (id : PathTime → PathTime) (Icc a b) =
      eVariationOn (Subtype.val : PathTime → ℝ) (Icc a b) := rfl
  rw [he]
  have hv := (hm.monotoneOn univ).eVariationOn_eq (mem_univ a) (mem_univ b)
  rw [univ_inter] at hv
  rw [hv]
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (b : ℝ) - a from sub_nonneg.mpr hab)]

variable {X : Type*} [MetricSpace X]

theorem lipschitz_pathLength_Icc_le (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Icc a b) ≤ L * edist b a := by
  rw [pathLengthMeasure_Icc γ hab]
  have h := hL.lipschitzOnWith.comp_eVariationOn_le (g := id) (s := Icc a b)
    (fun _ _ => mem_univ _)
  simpa only [Function.comp_id, variation_time_identity hab] using h

theorem lipschitz_pathLength_le_diameter (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (s : Set PathTime) :
    pathLengthMeasure γ s ≤ L * ediam s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : IsCompact (closure s) := isClosed_closure.isCompact
  obtain ⟨a, ha⟩ := hc.exists_isLeast hne.closure
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hne.closure
  have hab : a ≤ b := ha.2 hb.1
  have hs : s ⊆ Icc a b := fun t ht => ⟨ha.2 (subset_closure ht), hb.2 (subset_closure ht)⟩
  calc
    pathLengthMeasure γ s ≤ pathLengthMeasure γ (Icc a b) := measure_mono hs
    _ ≤ L * edist b a := lipschitz_pathLength_Icc_le γ hL hab
    _ ≤ L * ediam (closure s) := mul_le_mul' le_rfl (edist_le_ediam_of_mem hb.1 ha.1)
    _ = _ := by rw [ediam_closure]

theorem lipschitz_pathLength_le_hausdorff (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0) :
    pathLengthMeasure γ ≤ (L : ℝ≥0∞) • (μH[1] : Measure PathTime) := by
  have hL0' : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL0
  let μ : Measure PathTime := (L : ℝ≥0∞)⁻¹ • pathLengthMeasure γ
  have hμ : μ ≤ (μH[1] : Measure PathTime) := by
    apply Measure.le_hausdorffMeasure 1 μ ∞ (by simp)
    intro s _
    change (L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s ≤ ediam s ^ (1 : ℝ)
    rw [ENNReal.rpow_one]
    calc
      _ ≤ (L : ℝ≥0∞)⁻¹ * ((L : ℝ≥0∞) * ediam s) :=
        mul_le_mul' le_rfl (lipschitz_pathLength_le_diameter γ hL s)
      _ = ediam s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hL0' ENNReal.coe_ne_top, one_mul]
  apply Measure.le_iff.mpr
  intro s hs
  have h := mul_le_mul' (le_refl (L : ℝ≥0∞)) (hμ s)
  change (L : ℝ≥0∞) * ((L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s) ≤
    (L : ℝ≥0∞) * (μH[1] : Measure PathTime) s at h
  rwa [← mul_assoc, ENNReal.mul_inv_cancel hL0' ENNReal.coe_ne_top, one_mul] at h

end CircleDomainRigidity

end

end OAI
