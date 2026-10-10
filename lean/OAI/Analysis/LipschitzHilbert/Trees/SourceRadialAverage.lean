import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialLoss
import OAI.Analysis.LipschitzHilbert.Phase.AngularCommonTranslation

namespace OAI

/-! Averaging the literal radial majorants over one common translation
costs 4 epsilon times the total/self logarithm, independently of depth. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem radialBoundaryLoss_sum_integral (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1/2)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∫ b in (0:ℝ)..(1/2:ℝ), ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b) ≤
        2*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  let loss := fun b => ∑ i ∈ Finset.range N, Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
  have heq : (fun b => ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b) =
        (Ioo 0 epsilon).indicator loss := by
    funext b
    by_cases hb : b ∈ Ioo 0 epsilon
    · simp only [radialBoundaryLoss,indicator_of_mem hb]
      rfl
    · simp only [radialBoundaryLoss,indicator_of_notMem hb,Finset.sum_const_zero]
  rw [heq,intervalIntegral.integral_of_le (by norm_num),setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (show Ioo 0 epsilon ⊆ Ioc 0 (1/2:ℝ) from fun b hb =>
      ⟨hb.1,hb.2.le.trans hepsilon1⟩)]
  exact (g.radial_log_ratio_integral_le tops slope precision cutoff weight hp hw epsilon hepsilon
    N top htop he x).2

theorem radialBoundaryLoss_common_average (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1/2)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∫ origin in (0:ℝ)..g.rootWidth, ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
        ((g.withOrigin origin).boundaryDistance i (slope top)/g.width i)) / g.rootWidth ≤
      4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let f := fun i => g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
  let dist := fun i origin => (g.withOrigin origin).boundaryDistance i (slope top)/g.width i
  have hm (i : ℕ) : Measurable (dist i) := by
    simp only [dist,g.normalized_boundaryDistance_withOrigin]
    exact unitBoundaryDistance_measurable.comp ((measurable_const.sub measurable_id).div_const _)
  have hint (i : ℕ) (hi : i ∈ Finset.range N) :
      IntervalIntegrable (fun origin => f i (dist i origin)) volume 0 g.rootWidth := by
    have hib (a b : ℝ) : IntegrableOn (fun origin => f i (dist i origin)) (Ioc a b) volume := by
      apply (integrableOn_const (μ := volume) (C := B) (by simp)).mono'
        ((g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).comp (hm i)).aestronglyMeasurable
      filter_upwards [] with origin
      have hb := g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top
        htop (he i (Finset.mem_range.mp hi)) x (dist i origin)
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
      exact hb.2
    exact ⟨hib 0 g.rootWidth,hib g.rootWidth 0⟩
  have hhalf (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (f i) volume 0 (1/2:ℝ) :=
    g.radialBoundaryLoss_intervalIntegrable tops slope precision cutoff weight hp hw epsilon i top htop
      (he i (Finset.mem_range.mp hi)) x 0 (1/2)
  change (∫ origin in (0:ℝ)..g.rootWidth, ∑ i ∈ Finset.range N, f i (dist i origin))/g.rootWidth ≤ 4*epsilon*B
  rw [intervalIntegral.integral_finsetSum hint]
  have heq (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ origin in (0:ℝ)..g.rootWidth, f i (dist i origin)) =
        (2*g.rootWidth)*(∫ b in (0:ℝ)..(1/2:ℝ), f i b) :=
    g.common_translation_boundary_integral i (slope top) (f i) (hhalf i hi)
  rw [Finset.sum_congr rfl heq,← Finset.mul_sum,← intervalIntegral.integral_finsetSum hhalf]
  apply (div_le_iff₀ g.rootWidth_pos).mpr
  have hb := g.radialBoundaryLoss_sum_integral tops slope precision cutoff weight hp hw epsilon
    hepsilon hepsilon1 N top htop he x
  change (∫ b in (0:ℝ)..(1/2:ℝ), ∑ i ∈ Finset.range N, f i b) ≤ 2*epsilon*B at hb
  have hc : 0 ≤ (2:ℝ)*g.rootWidth := mul_nonneg (by norm_num) g.rootWidth_pos.le
  have h := mul_le_mul_of_nonneg_left hb hc
  nlinarith

end LipschitzHilbert.AngularGrid

end

end OAI
