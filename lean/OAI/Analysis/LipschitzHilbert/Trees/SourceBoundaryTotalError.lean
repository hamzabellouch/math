import OAI.Analysis.LipschitzHilbert.Packets.SourceBoundaryPacketRegroup

namespace OAI

/-! The actual original-minus-central finite packet sum is controlled
by the sum of the individual top entropy costs. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_total_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (M : τ → ℕ)
    (he : ∀ t ∈ tops, g.eligible cutoff (precision t) (M t))
    (a : ℝ) (ha : 0 ≤ a) (x : X) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : σ → E)
    (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (B : τ → ℝ) (hB0 : ∀ t ∈ tops, 0 ≤ B t)
    (hB : ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value s‖ ≤ B t) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let original := ∑ s ∈ packets, value s
    let central := fun origin => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s
    let err := fun origin => ‖original-central origin‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*epsilon*(∑ t ∈ tops, B t*Real.log ((∑ u ∈ tops, weight u x)/weight t x)) := by
  intro epsilon original central err
  let e := fun t origin => ∑ s ∈ packets.filter (fun s => assigned s = t),
    ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
      (g.sourceBoundaryGap L) (stop s) t a x : ℝ):ℂ) • value s
  have ht (t : τ) (ht : t ∈ tops) :
      IntervalIntegrable (fun origin => ‖e t origin‖) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ‖e t origin‖)/g.rootWidth ≤
        8*a*B t*epsilon*Real.log ((∑ u ∈ tops, weight u x)/weight t x) := by
    apply g.source_boundary_expected_finite_packet_error L hbranch hsmall tops slope precision cutoff
      weight hp hw hK (M t) t ht (he t ht) a ha x (packets.filter (fun s => assigned s = t))
      stop value _ (B t) (hB0 t ht) (hB t ht)
    intro s hs
    obtain ⟨hsp,hst⟩ := Finset.mem_filter.mp hs
    simpa only [hst] using hmax s hsp
  have heq (origin : ℝ) : original-central origin = ∑ t ∈ tops, e t origin := by
    calc
      original-central origin = ∑ s ∈ packets,
          ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
            (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s := by
        dsimp only [original,central]
        rw [←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s _
        rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
      _ = ∑ t ∈ tops, e t origin := by
        rw [←Finset.sum_fiberwise_of_maps_to hassigned]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s hs
        rw [(Finset.mem_filter.mp hs).2]
  have hm : Measurable err := by
    apply Measurable.norm
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro s hs
    apply Measurable.smul _ measurable_const
    exact Complex.continuous_ofReal.measurable.comp
      (g.measurable_sourceBoundaryCoefficient_withOrigin tops slope precision cutoff weight hp hw hK
        (g.sourceBoundaryGap L) (stop s) (assigned s) (hassigned s hs)
        (g.eligible_of_le (hp (assigned s) (hassigned s hs)) (hmax s hs)
          (he (assigned s) (hassigned s hs))) a x)
  have hle (origin : ℝ) : err origin ≤ ∑ t ∈ tops, ‖e t origin‖ := by
    dsimp only [err]
    rw [heq]
    exact norm_sum_le _ _
  have hsum : IntervalIntegrable (fun origin => ∑ t ∈ tops, ‖e t origin‖) volume 0 g.rootWidth := by
    convert IntervalIntegrable.sum tops (fun t ht' => (ht t ht').1) using 1
    ext origin
    simp only [Finset.sum_apply]
  have hi : IntervalIntegrable err volume 0 g.rootWidth := by
    apply hsum.mono_fun' hm.aestronglyMeasurable
    filter_upwards [] with origin
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ err origin from norm_nonneg _)] using hle origin
  refine ⟨hi,?_⟩
  have hh := intervalIntegral.integral_mono g.rootWidth_pos.le hi hsum hle
  apply (div_le_div_of_nonneg_right hh g.rootWidth_pos.le).trans
  rw [intervalIntegral.integral_finsetSum (fun t ht' => (ht t ht').1),Finset.sum_div]
  calc
    _ ≤ ∑ t ∈ tops, 8*a*B t*epsilon*Real.log ((∑ u ∈ tops, weight u x)/weight t x) :=
      Finset.sum_le_sum (fun t ht' => (ht t ht').2)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

end LipschitzHilbert.AngularGrid

end

end OAI
