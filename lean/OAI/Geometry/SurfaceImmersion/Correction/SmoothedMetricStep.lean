import OAI.Geometry.SurfaceImmersion.Correction.SmoothingMetricCrossBounds

namespace OAI

/-! The normalized defect of the actual unsmoothed map update. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.ExactCorrection
open FiniteOrderSmoothing WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalizedMetricDefect (target : Base → ℝ) (δ : ℝ) (G : Base → V)
    (v w : Base) : Base → ℝ := fun x => (target x - pullbackMetric G x v w) / δ ^ 2

def realizedMetricError (target Hs : Base → ℝ) (δ δ' : ℝ)
    (G U : Base → V) (v w : Base) : Base → ℝ := fun x =>
  pullbackMetric (G + U) x v w - pullbackMetric G x v w -
    (δ ^ 2 * Hs x - δ' ^ 2 * target x)

lemma contDiff_pullbackMetric {G : Base → V} (hG : ContDiff ℝ ∞ G) (v w : Base) :
    ContDiff ℝ ∞ (fun x => pullbackMetric G x v w) := by
  have hd := hG.fderiv_right (m := ∞) (by simp)
  exact ContDiff.inner ℝ (hd.clm_apply contDiff_const) (hd.clm_apply contDiff_const)

lemma contDiff_metricCrossTerm {G U : Base → V}
    (hG : ContDiff ℝ ∞ G) (hU : ContDiff ℝ ∞ U) (v w : Base) :
    ContDiff ℝ ∞ (fun x => metricCrossTerm G U x v w) := by
  have hdG := hG.fderiv_right (m := ∞) (by simp)
  have hdU := hU.fderiv_right (m := ∞) (by simp)
  exact (ContDiff.inner ℝ (hdG.clm_apply contDiff_const) (hdU.clm_apply contDiff_const)).add
    (ContDiff.inner ℝ (hdG.clm_apply contDiff_const) (hdU.clm_apply contDiff_const))

lemma contDiff_normalizedMetricDefect {target : Base → ℝ} (ht : ContDiff ℝ ∞ target)
    (δ : ℝ) {G : Base → V} (hG : ContDiff ℝ ∞ G) (v w : Base) :
    ContDiff ℝ ∞ (normalizedMetricDefect target δ G v w) :=
  (ht.sub (contDiff_pullbackMetric hG v w)).div_const _

lemma contDiff_realizedMetricError {target Hs : Base → ℝ}
    (ht : ContDiff ℝ ∞ target) (hs : ContDiff ℝ ∞ Hs) (δ δ' : ℝ)
    {G U : Base → V} (hG : ContDiff ℝ ∞ G) (hU : ContDiff ℝ ∞ U) (v w : Base) :
    ContDiff ℝ ∞ (realizedMetricError target Hs δ δ' G U v w) :=
  ((contDiff_pullbackMetric (hG.add hU) v w).sub (contDiff_pullbackMetric hG v w)).sub
    ((contDiff_const.mul hs).sub (contDiff_const.mul ht))

/-- The chosen error of the smoothed realization controls the actual new
normalized defect. This is an identity of concrete maps, before estimates. -/
theorem actual_normalized_defect_identity {target Hs : Base → ℝ}
    {δ δ' : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    {G S U : Base → V} (hG : ContDiff ℝ ∞ G) (hS : ContDiff ℝ ∞ S)
    (hU : ContDiff ℝ ∞ U) (v w : Base) (x : Base) :
    δ' ^ 2 * (normalizedMetricDefect target δ' (G + U) v w x - target x) =
      δ ^ 2 * (normalizedMetricDefect target δ G v w x - Hs x) -
        realizedMetricError target Hs δ δ' S U v w x - metricCrossTerm (G - S) U x v w := by
  apply normalized_defect_identity (hG.differentiable (by simp) x)
    (hS.differentiable (by simp) x) (hU.differentiable (by simp) x) v w
  · exact mul_div_cancel₀ _ (pow_ne_zero 2 hδ)
  · exact mul_div_cancel₀ _ (pow_ne_zero 2 hδ')
  · rfl

/-- Weighted estimate for a complete normalized metric update. The three
bounds are on the concrete smoothing tail, realization error and cross term. -/
theorem normalized_metric_step_bound {target Hs : Base → ℝ}
    (ht : ContDiff ℝ ∞ target) (hs : ContDiff ℝ ∞ Hs)
    {δ δ' τ BH BE BC : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) (hτ : 0 ≤ τ) (m : ℕ)
    {G S U : Base → V} (hG : ContDiff ℝ ∞ G) (hS : ContDiff ℝ ∞ S)
    (hU : ContDiff ℝ ∞ U) (v w : Base)
    (hbH : WeightedBound Set.univ τ m BH (normalizedMetricDefect target δ G v w - Hs))
    (hbE : WeightedBound Set.univ τ m BE (realizedMetricError target Hs δ δ' S U v w))
    (hbC : WeightedBound Set.univ τ m BC (fun x => metricCrossTerm (G - S) U x v w)) :
    WeightedBound Set.univ τ m ((δ' ^ 2)⁻¹ * (δ ^ 2 * BH + BE + BC))
      (normalizedMetricDefect target δ' (G + U) v w - target) := by
  have hH := (contDiff_normalizedMetricDefect ht δ hG v w).sub hs
  have hE := contDiff_realizedMetricError ht hs δ δ' hS hU v w
  have hC := contDiff_metricCrossTerm (hG.sub hS) hU v w
  have h₁ := hbH.const_smul isOpen_univ.uniqueDiffOn hH.contDiffOn (δ ^ 2)
  simp only [abs_of_nonneg (sq_nonneg δ)] at h₁
  have h₂ := h₁.sub isOpen_univ.uniqueDiffOn hτ (hH.const_smul (δ ^ 2)).contDiffOn
    hE.contDiffOn hbE
  have h₃ := h₂.sub isOpen_univ.uniqueDiffOn hτ
    ((hH.const_smul (δ ^ 2)).sub hE).contDiffOn hC.contDiffOn hbC
  have h₄ := h₃.const_smul isOpen_univ.uniqueDiffOn
    (((hH.const_smul (δ ^ 2)).sub hE).sub hC).contDiffOn ((δ' ^ 2)⁻¹)
  simp only [abs_inv, abs_of_nonneg (sq_nonneg δ')] at h₄
  apply h₄.congr
  intro x _
  have hi := actual_normalized_defect_identity (target := target) (Hs := Hs)
    hδ hδ' hG hS hU v w x
  change normalizedMetricDefect target δ' (G + U) v w x - target x =
    (δ' ^ 2)⁻¹ * _
  simp only [smul_eq_mul]
  have hi' := congrArg (fun a : ℝ => (δ' ^ 2)⁻¹ * a) hi
  rw [inv_mul_cancel_left₀ (pow_ne_zero 2 hδ')] at hi'
  exact hi'

end ClosedSurfaceR4.ExactCorrection

end

end OAI
