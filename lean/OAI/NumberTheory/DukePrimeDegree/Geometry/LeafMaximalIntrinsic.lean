import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafMaximalDisintegration

namespace OAI

/-!
# Relative maximal estimates for intrinsic leaves in a root box

Normalization does not change a relative mass inequality. On an interval
contained in a root box, the intrinsic leaf therefore gives the same
relative bound as the box's conditional probability measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma basedRealMeasure_translate_apply (ν : Measure ℝ) (t : ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) =
      (ν (ball t 1))⁻¹ * ν S := by
  change (centerRealMeasure ν t (ball 0 1))⁻¹ *
    centerRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) = _
  have hpre : MeasurableSet ((fun u : ℝ => t + u) ⁻¹' S) :=
    hS.preimage (show Measurable (fun u : ℝ => t + u) by fun_prop)
  rw [centerRealMeasure_ball, centerRealMeasure,
    Measure.map_apply (Homeomorph.subRight t).measurable hpre]
  have he : (Homeomorph.subRight t) ⁻¹' ((fun u : ℝ => t + u) ⁻¹' S) = S := by
    ext u
    change (t + (u - t) ∈ S ↔ u ∈ S)
    rw [show t + (u - t) = u by ring]
  rw [he]

lemma smul_relative_mass_iff (ν : Measure ℝ) (a c : ℝ≥0∞)
    (ha : a ≠ 0) (haTop : a ≠ ∞) (S T : Set ℝ) :
    c * (a * ν S) ≤ a * ν T ↔ c * ν S ≤ ν T := by
  constructor
  · intro h
    have hh := mul_le_mul' (le_refl a⁻¹) h
    simpa only [mul_left_comm a⁻¹ c, ← mul_assoc a⁻¹ a,
      ENNReal.inv_mul_cancel ha haTop, one_mul] using hh
  · intro h
    have hh := mul_le_mul' (le_refl a) h
    simpa only [mul_left_comm a c] using hh

lemma basedRealMeasure_relative_mass_iff (ν : Measure ℝ)
    [IsLocallyFiniteMeasure ν] (t : ℝ) (ht : 0 < ν (ball t 1))
    (c : ℝ≥0∞) (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    c * basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) ≤
      basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' T) ↔ c * ν S ≤ ν T := by
  rw [basedRealMeasure_translate_apply ν t S hS,
    basedRealMeasure_translate_apply ν t T hT]
  exact smul_relative_mass_iff ν _ c (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (ENNReal.inv_ne_top.mpr ht.ne') S T

lemma preimage_add_closedBall (t r : ℝ) :
    (fun u : ℝ => t + u) ⁻¹' closedBall t r = closedBall 0 r := by
  ext u
  simp only [mem_preimage, mem_closedBall, Real.dist_eq, add_sub_cancel_left, sub_zero]

/-- If an intrinsic bad interval stays inside the root box, its
relative mass inequality passes to the actual conditional kernel. -/
lemma intrinsic_bad_interval_to_conditional
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (A : RootBox hij k) (R : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : RootSlice i j k) (t r : ℝ) (E : Set (X n)) (hE : MeasurableSet E)
    (hs : A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s))
    (ht : 0 < A.leafMeasure R μ s (ball t 1))
    (heq : intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t)) =
      A.basedLeaf R μ (s, t))
    (hr : closedBall t r ⊆ A.time) (c : ℝ≥0∞)
    (hbad : c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t))
        (closedBall 0 r) ≤
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t))
        ({u | rightAction (rootQuotientParametrization hij (s, t))
          (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r)) :
    c * A.conditionalKernel μ s (closedBall t r) ≤
      A.conditionalKernel μ s
        ({u | rootQuotientParametrization hij (s, u) ∈ E} ∩ closedBall t r) := by
  let ν := A.leafMeasure R μ s
  let : IsLocallyFiniteMeasure ν := hs.1
  let F : Set ℝ := {u | rootQuotientParametrization hij (s, u) ∈ E}
  have hF : MeasurableSet F := hE.preimage
    ((rootQuotientParametrization_localHomeomorph hij).continuous.measurable.comp
      (measurable_const.prodMk measurable_id))
  have htranslate : (fun u : ℝ => t + u) ⁻¹' (F ∩ closedBall t r) =
      {u | rightAction (rootQuotientParametrization hij (s, t))
        (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r := by
    rw [preimage_inter, preimage_add_closedBall]
    congr 1
    ext u
    simp only [mem_preimage, mem_ofPred_eq, F, rootQuotientParametrization_add]
  have hmass : c * ν (closedBall t r) ≤ ν (F ∩ closedBall t r) := by
    apply (basedRealMeasure_relative_mass_iff ν t ht c _ _
      isClosed_closedBall.measurableSet (hF.inter isClosed_closedBall.measurableSet)).mp
    rw [preimage_add_closedBall, htranslate]
    simpa only [heq, RootBox.basedLeaf] using hbad
  have hcond := hs.2.2.1
  rw [← hcond, Measure.restrict_apply isClosed_closedBall.measurableSet,
    Measure.restrict_apply (hF.inter isClosed_closedBall.measurableSet),
    inter_eq_left.mpr hr, inter_eq_left.mpr (inter_subset_right.trans hr)]
  exact hmass

end DukePrimeDegree

end

end OAI
