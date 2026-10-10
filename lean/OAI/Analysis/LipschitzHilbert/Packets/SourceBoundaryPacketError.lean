import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryExpectedLoss
import OAI.Analysis.LipschitzHilbert.Estimates.MonotoneCoefficientSum

namespace OAI

/-! Boundary coefficient deficits acting on the original stopping bands.
The bound uses their raw prefix sums, with no loss in the number of levels. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourceBoundaryCoefficient_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N)
    (a : ℝ) (ha : 0 ≤ a) (x : X) :
    0 < g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ∧
      g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ≤ 1 := by
  constructor
  · rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top htop he a x]
    exact Real.exp_pos _
  · have h := g.sourceBoundaryCoefficient_antitone tops slope precision cutoff weight hp hw hK gap
      (Nat.zero_le N) top htop he a ha x
    simpa only [sourceBoundaryCoefficient,Finset.range_zero,Finset.prod_empty] using h

theorem measurable_sourceBoundaryLogLoss_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).sourceBoundaryLogLoss
      tops slope precision cutoff weight K gap N top x) := by
  unfold sourceBoundaryLogLoss
  apply Finset.measurable_sum
  intro i _
  exact g.measurable_source_boundary_log_loss_withOrigin tops slope precision cutoff weight hK gap i (slope top) x

theorem measurable_sourceBoundaryCoefficient_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a x) := by
  have heq : (fun origin => (g.withOrigin origin).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a x) =
      (fun origin => Real.exp (-a*(g.withOrigin origin).sourceBoundaryLogLoss
        tops slope precision cutoff weight K gap N top x)) := by
    funext origin
    exact (g.withOrigin origin).sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight
      hp hw hK gap N top htop he a x
  rw [heq]
  exact (measurable_const.mul (g.measurable_sourceBoundaryLogLoss_withOrigin tops slope precision
    cutoff weight hK gap N top x)).exp

theorem source_boundary_deficit_sum_le_log_loss (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N)
    (a : ℝ) (ha : 0 ≤ a) (x : X) (f : ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ N, ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (N+1),
      ((1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap j top a x : ℝ):ℂ) • f j‖ ≤
      2*a*B*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x := by
  let w := fun j => 1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap j top a x
  have hnonneg (j : ℕ) (hj : j ≤ N) : 0 ≤ w j :=
    sub_nonneg.mpr (g.sourceBoundaryCoefficient_bounds tops slope precision cutoff weight hp hw hK gap
      j top htop (g.eligible_of_le (hp top htop) hj he) a ha x).2
  have hmono (i : ℕ) (_hi : i ≤ N) (j : ℕ) (hj : j ≤ N) (hij : i ≤ j) : w i ≤ w j := by
    exact sub_le_sub_left (g.sourceBoundaryCoefficient_antitone tops slope precision cutoff weight
      hp hw hK gap hij top htop (g.eligible_of_le (hp top htop) hj he) a ha x) 1
  have h := norm_monotone_coefficient_sum w f N B hB0 hnonneg hmono hB
  apply h.trans
  have hd := mul_le_mul_of_nonneg_left (g.sourceBoundaryCoefficient_deficit_le tops slope precision
    cutoff weight hp hw hK gap N top htop he a x) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB0)
  dsimp only [w]
  nlinarith only [hd]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_packet_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (a : ℝ) (ha : 0 ≤ a)
    (x : X) (f : ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ N, ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖∑ j ∈ Finset.range (N+1),
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) j top a x : ℝ):ℂ) • f j‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*B*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon err
  let loss := fun origin => (g.withOrigin origin).sourceBoundaryLogLoss tops slope precision cutoff
    weight K (g.sourceBoundaryGap L) N top x
  have hl := g.source_boundary_expected_log_loss L hbranch hsmall tops slope precision cutoff weight
    hp hw hK N top htop (fun i hi => g.eligible_of_le (hp top htop) hi.le he) x
  have hbound (origin : ℝ) : err origin ≤ (2*a*B)*loss origin :=
    (g.withOrigin origin).source_boundary_deficit_sum_le_log_loss tops slope precision cutoff weight
      hp hw hK (g.sourceBoundaryGap L) N top htop he a ha x f B hB0 hB
  have hm : Measurable err := by
    apply Measurable.norm
    apply Finset.measurable_sum
    intro j hj
    apply Measurable.smul _ measurable_const
    exact (Complex.continuous_ofReal.measurable.comp
      (measurable_const.sub (g.measurable_sourceBoundaryCoefficient_withOrigin tops slope precision
        cutoff weight hp hw hK (g.sourceBoundaryGap L) j top htop
        (g.eligible_of_le (hp top htop) (by have := Finset.mem_range.mp hj; omega) he) a x)))
  have hc : 0 ≤ 2*a*B := mul_nonneg (mul_nonneg (by norm_num) ha) hB0
  have hi : IntervalIntegrable err volume 0 g.rootWidth := by
    apply (hl.1.const_mul (2*a*B)).mono_fun' hm.aestronglyMeasurable
    filter_upwards [] with origin
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ err origin from norm_nonneg _)] using hbound origin
  refine ⟨hi,?_⟩
  have hh := intervalIntegral.integral_mono g.rootWidth_pos.le hi (hl.1.const_mul (2*a*B)) hbound
  rw [intervalIntegral.integral_const_mul] at hh
  have hh' := div_le_div_of_nonneg_right hh g.rootWidth_pos.le
  have hh'' := mul_le_mul_of_nonneg_left hl.2 hc
  calc
    (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        (2*a*B)*((∫ origin in (0:ℝ)..g.rootWidth, loss origin)/g.rootWidth) := by
      convert hh' using 1; ring
    _ ≤ (2*a*B)*(4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x)) := hh''
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
