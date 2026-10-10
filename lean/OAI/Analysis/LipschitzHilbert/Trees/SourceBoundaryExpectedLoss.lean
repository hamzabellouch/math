import OAI.Analysis.LipschitzHilbert.Phase.AngularTranslationMeasurable
import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundaryNull
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryMajorant
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryLossBounds
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryDeficit
import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialAverage

namespace OAI

/-! Expected logarithmic boundary loss for the literal source coefficients.
Only one common angular translation is averaged; the eligibility cutoff
and the terminal path length are retained. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem source_boundary_expected_log_loss (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let loss := fun origin => (g.withOrigin origin).sourceBoundaryLogLoss tops slope precision cutoff
      weight K (g.sourceBoundaryGap L) N top x
    IntervalIntegrable loss volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, loss origin)/g.rootWidth ≤
        4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon loss
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let ell := fun i origin => Real.log
    ((g.withOrigin origin).sourceBoundaryMass tops slope precision cutoff weight K
      (g.sourceBoundaryGap L) i ((g.withOrigin origin).index (i+1) (slope top)) x /
      (g.withOrigin origin).mass tops slope precision cutoff weight i
        ((g.withOrigin origin).index i (slope top)) x)
  let major := fun i origin => g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
    ((g.withOrigin origin).boundaryDistance i (slope top)/g.width i)
  have hbounded (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ u, 0 ≤ f u ∧ f u ≤ B) :
      IntervalIntegrable f volume 0 g.rootWidth := by
    have hint (a b : ℝ) : IntegrableOn f (Ioc a b) volume := by
      apply (integrableOn_const (μ := volume) (C := B) (by simp)).mono' hf.aestronglyMeasurable
      filter_upwards [] with u
      rw [Real.norm_eq_abs,abs_of_nonneg (hb u).1]
      exact (hb u).2
    exact ⟨hint 0 g.rootWidth,hint g.rootWidth 0⟩
  have hel (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (ell i) volume 0 g.rootWidth := by
    apply hbounded
    · exact g.measurable_source_boundary_log_loss_withOrigin tops slope precision cutoff weight hK
        (g.sourceBoundaryGap L) i (slope top) x
    · intro origin
      exact (g.withOrigin origin).source_boundary_log_loss_bounds tops slope precision cutoff weight
        hp hw hK (g.sourceBoundaryGap L) i top htop (he i (Finset.mem_range.mp hi)) x
  have hmajor (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (major i) volume 0 g.rootWidth := by
    apply hbounded
    · apply (g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).comp
      simp only [normalized_boundaryDistance_withOrigin]
      exact unitBoundaryDistance_measurable.comp ((measurable_const.sub measurable_id).div_const _)
    · intro origin
      exact g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top htop
        (he i (Finset.mem_range.mp hi)) x _
  have hae (i : ℕ) (hi : i ∈ Finset.range N) : ∀ᵐ origin, ell i origin ≤ major i origin := by
    filter_upwards [g.ae_normalized_boundaryDistance_pos i (slope top)] with origin ho
    exact (g.withOrigin origin).source_boundary_log_loss_le_majorant L hbranch tops slope precision cutoff
      weight hp hw hK i top htop (he i (Finset.mem_range.mp hi)) x ho
  have hsum : ∀ᵐ origin, (∑ i ∈ Finset.range N, ell i origin) ≤ ∑ i ∈ Finset.range N, major i origin := by
    have hforall := ae_all_iff.mpr fun i : Fin N => hae i (Finset.mem_range.mpr i.isLt)
    filter_upwards [hforall] with origin ho
    exact Finset.sum_le_sum fun i hi => ho ⟨i,Finset.mem_range.mp hi⟩
  have hi : IntervalIntegrable loss volume 0 g.rootWidth := by
    change IntervalIntegrable (fun origin => ∑ i ∈ Finset.range N, ell i origin) volume 0 g.rootWidth
    convert IntervalIntegrable.sum (Finset.range N) hel using 1
    ext origin
    simp only [Finset.sum_apply]
  refine ⟨hi,?_⟩
  have hm : IntervalIntegrable (fun origin => ∑ i ∈ Finset.range N, major i origin) volume 0 g.rootWidth := by
    convert IntervalIntegrable.sum (Finset.range N) hmajor using 1
    ext origin
    simp only [Finset.sum_apply]
  have hb := intervalIntegral.integral_mono_ae g.rootWidth_pos.le hi hm hsum
  apply (div_le_div_of_nonneg_right hb g.rootWidth_pos.le).trans
  exact g.radialBoundaryLoss_common_average tops slope precision cutoff weight hp hw epsilon
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _)) hsmall N top htop he x

end LipschitzHilbert.AngularGrid

end

end OAI
