import Mathlib
import OAI.Probability.SLE.StochasticFubini
import OAI.Probability.SLE.WindowTails

namespace OAI

/-! Stopped Fields for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
lemma boundedSpatialHit_antitone_radius {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (hεr : ε ≤ r) (hs : r ≤ dist (γ 0) z) (T : ℝ≥0) :
    boundedSpatialHit γ z r T ≤ boundedSpatialHit γ z ε T := by
  apply WithTop.coe_le_coe.mp
  rw [boundedSpatialHit_coe, boundedSpatialHit_coe]
  exact min_le_min (spatialHitTime_antitone_radius hc z hεr hs) le_rfl

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

lemma joint_spatialHit_stopping {Z : Type*} [mZ : MeasurableSpace Z]
    (z : Z → ℂ) (hz : Measurable z) (r : ℝ) :
    IsStoppingTime (spatialFiltration (Z := Z) a.filtration)
      (fun p : Z × a.samples => spatialHitTime (γ p.2) (z p.1) r) := by
  let H (t : ℝ≥0) (p : Z × a.samples) := dist (γ p.2 t) (z p.1) - r
  have ha : Adapted (spatialFiltration (Z := Z) a.filtration) H := by
    intro t
    have hm := a.trace_adapted t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((hm.comp measurable_snd).dist (hz.comp measurable_fst)).sub_const r
  have hc (p : Z × a.samples) : Continuous (fun t => H t p) :=
    ((a.trace_continuous p.2).dist continuous_const).sub continuous_const
  exact continuous_zero_hit_stopping (spatialFiltration (Z := Z) a.filtration) H ha hc 0

lemma joint_boundedSpatialHit_stopping {Z : Type*} [mZ : MeasurableSpace Z]
    (z : Z → ℂ) (hz : Measurable z) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime (spatialFiltration (Z := Z) a.filtration)
      (fun p : Z × a.samples => (boundedSpatialHit (γ p.2) (z p.1) r T : WithTop ℝ≥0)) := by
  simpa only [boundedSpatialHit_coe] using (a.joint_spatialHit_stopping z hz r).min_const T

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma clipped_spatial_window_coefficient_le
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (ω : Ω) (α S : ℝ≥0)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hin : ∀ t : ℝ≥0, t ≤ α → lo ≤ ((c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((c (initialLogCoordinates z)).Q t ω).1.im ≤ hi)
    (r ε : ℝ) (t : ℝ≥0) :
    |(if min (boundedSpatialHit γ z r S) α ≤ t ∧
        t < min (boundedSpatialHit γ z ε S) α then
      greenLogCoefficient κ ((c (initialLogCoordinates z)).Q t ω) (B t ω) else 0)| ≤
    |spatialSlabCoefficient κ (fun s => Real.sqrt κ * B s ω) γ G r ε t z| := by
  split_ifs with ht
  · have hta : t < α := ht.2.trans_le (min_le_right _ _)
    have hte : t < boundedSpatialHit γ z ε S := ht.2.trans_le (min_le_left _ _)
    have htS : t < S := by
      apply WithTop.coe_lt_coe.mp
      exact (WithTop.coe_lt_coe.mpr hte).trans_le
        (by rw [boundedSpatialHit_coe]; exact min_le_right _ _)
    have hsr : boundedSpatialHit γ z r S ≤ t := (min_le_iff.mp ht.1).resolve_right (not_le_of_gt hta)
    have hr : spatialHitTime γ z r ≤ t := by
      have hh := WithTop.coe_le_coe.mpr hsr
      rw [boundedSpatialHit_coe] at hh
      exact (min_le_iff.mp hh).resolve_right (not_le_of_gt (WithTop.coe_lt_coe.mpr htS))
    have he : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε :=
      (WithTop.coe_le_coe.mpr hte.le).trans (boundedSpatialHit_le γ z ε S)
    obtain ⟨hl, hq⟩ := clipped_chart_identification c hBc z hz ω α γ G F hw hin
    have hlive := survivingDomain_antitone γ hta.le hl
    rw [hq t hta.le, greenLogCoefficient_logCoordinates ((hBc ω).const_mul _) hw κ _ z t hlive rfl,
      spatialSlabCoefficient, ite_eq_left ⟨hr, he, hlive⟩]
  · simpa only [abs_zero] using abs_nonneg (spatialSlabCoefficient κ (fun s => Real.sqrt κ * B s ω) γ G r ε t z)

 

theorem IsCapacityTwoWitness.spatial_masked_bracket_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im)
    (b : ℝ → A → ℝ)
    (hb : ∀ t, 0 ≤ t → ∀ z, |b t z| ≤
      |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal
      ((∫ z, b t z ∂(volume.comap (Subtype.val : A → ℂ))) ^ 2)) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  apply le_trans _ (h.spatial_slab_absolute_bracket_bound hU hκ hκ4 hε hr A hA hheight)
  apply setLIntegral_mono' measurableSet_Ici
  intro t ht
  apply (spatial_integral_square_le (volume.comap (Subtype.val : A → ℂ)) (b t)).trans
  apply pow_le_pow_left₀ bot_le
  calc
    _ ≤ ∫⁻ z : A, ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|
        ∂(volume.comap (Subtype.val : A → ℂ)) := lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hb t ht z)
    _ = _ := lintegral_subtype_comap (μ := (volume : Measure ℂ)) hA (fun z : ℂ => ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma clipped_family_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) :
    ∃ L : ℝ≥0, ∀ (q : ℂ × ℝ) (ω : Ω) (t : ℝ≥0),
      ‖(c q).Q t ω‖ ≤ ‖q‖ + L * t := by
  obtain ⟨L, K, hb, hK⟩ := clippedLogLoewnerField_bounds lo hi hle
  refine ⟨L, fun q ω t => ?_⟩
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => (c q).Q s ω) (a := (0 : ℝ)) (b := (t : ℝ))
    (f' := fun s => clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω) ((c q).Q s ω))
    (fun s hs => ((c q).derivative ω s hs.1).mono (fun _ hx => hx.1))
    (fun s hs => hb _ _) (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  rw [(c q).initial, sub_zero] at hh
  calc
    _ ≤ ‖q‖ + ‖(c q).Q t ω - q‖ := by
      simpa only [add_comm] using norm_le_insert' ((c q).Q t ω) q
    _ ≤ _ := by linarith

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem spatial_angular_cutoff
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ lo hi : ℝ) (hle : lo ≤ hi)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q) (hq0 : ∀ z, (q z).2 = 0)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ∀ z, ε ≤ logAngleSq κ (q z) 0)
    (hlo : ∀ z, lo < (q z).1.im - u / (2 * ε)) (hhi : ∀ z, (q z).1.im < hi)
    (T : ℝ≥0) (hT : ∀ z, u < (4 * ε ^ 2 / Real.exp (2 * (q z).1.im)) * T) :
    ∃ τ : Z × Ω → ℝ≥0,
      IsStoppingTime (spatialFiltration (Z := Z)
        (Filtration.natural B (fun t => (hm t).stronglyMeasurable)))
        (fun p => (τ p : WithTop ℝ≥0)) ∧
      (∀ z ω, τ (z,ω) < T) ∧
      (∀ z ω t, t ≤ τ (z,ω) →
        logRadiusClock (q z).1.im ((c (q z)).Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi) ∧
      (∀ z ω t, t < τ (z,ω) →
        logRadiusClock (q z).1.im ((c (q z)).Q t ω) < u ∧
        ε < logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
        lo < ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im < hi) ∧
      (∀ z ω, logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) = u ∨
        logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) = ε) := by
  let f := spatialFiltration (Z := Z) (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
  let D (t : ℝ≥0) (p : Z × Ω) :=
    min (u - logRadiusClock (q p.1).1.im ((c (q p.1)).Q t p.2))
      (min (logAngleSq κ ((c (q p.1)).Q t p.2) (B t p.2) - ε)
        (min (((c (q p.1)).Q t p.2).1.im - lo) (hi - ((c (q p.1)).Q t p.2).1.im)))
  have hDa : Adapted f D := by
    intro t
    have hQ := clipped_family_past_measurable c t
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) t
    have hc := hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)
    have hBb := hBa.comp (@measurable_snd Z Ω mZ _)
    have hη := Complex.continuous_im.measurable.comp (hq.comp (@measurable_fst Z Ω mZ (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))).fst
    have hclock := (hη.sub (Complex.continuous_im.measurable.comp hc.fst)).add hc.snd
    exact (measurable_const.sub hclock).min
      ((((continuous_logAngleSq κ).measurable.comp (hc.prodMk hBb)).sub_const ε).min
        (((Complex.continuous_im.measurable.comp hc.fst).sub_const lo).min
          (measurable_const.sub (Complex.continuous_im.measurable.comp hc.fst))))
  have hDc (p : Z × Ω) : Continuous (fun t => D t p) := by
    have hc := ((c (q p.1)).lipschitz p.2).continuous.comp NNReal.continuous_coe
    exact (continuous_const.sub ((continuous_const.sub (Complex.continuous_im.comp hc.fst)).add hc.snd)).min
      ((((continuous_logAngleSq κ).comp (hc.prodMk (hBc p.2))).sub continuous_const).min
        (((Complex.continuous_im.comp hc.fst).sub continuous_const).min
          (continuous_const.sub (Complex.continuous_im.comp hc.fst))))
  have hD0 (p : Z × Ω) : 0 ≤ D 0 p := by
    dsimp only [D]
    rw [NNReal.coe_zero, (c (q p.1)).initial, hB0]
    simp only [le_min_iff, sub_nonneg]
    refine ⟨?_, hε0 p.1, ?_, (hhi p.1).le⟩
    · simpa only [logRadiusClock, sub_self, zero_add, hq0] using hu
    · have hd : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
      linarith [hlo p.1]
  obtain ⟨τ, hτ, hb, hleD, hltD, hzero⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin (z : Z) (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ (z,ω)) :
      logRadiusClock (q z).1.im ((c (q z)).Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
      lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi :=
    by simpa only [D, le_min_iff, sub_nonneg] using hleD (z,ω) t ht
  have hg (z : Z) (ω : Ω) :
      ((c (q z)).Q (τ (z,ω)) ω).1.im ≤ (q z).1.im ∧
      (q z).1.im - logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) / (2 * ε) ≤ ((c (q z)).Q (τ (z,ω)) ω).1.im ∧
      (4 * ε ^ 2 / Real.exp (2 * (q z).1.im)) * τ (z,ω) ≤ logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 (τ (z,ω) : ℝ)) :
        HasDerivWithinAt (fun t => (c (q z)).Q t ω)
          (physicalLogLoewnerField (Real.sqrt κ * B s.toNNReal ω) ((c (q z)).Q s ω))
          (Icc 0 (τ (z,ω) : ℝ)) s := by
      have hst : s.toNNReal ≤ τ (z,ω) := Real.toNNReal_le_iff_le_coe.mpr hs.2
      have hbounds := (hin z ω s.toNNReal hst).2.2
      rw [Real.coe_toNNReal _ hs.1] at hbounds
      have hh := ((c (q z)).derivative ω s hs.1).mono (show Icc (0 : ℝ) (τ (z,ω) : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
      rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hbounds.1, hbounds.2⟩] at hh
    have ha (s : ℝ) (hs : s ∈ Icc 0 (τ (z,ω) : ℝ)) :
        ε ≤ logAngleSq κ ((c (q z)).Q s ω) (B s.toNNReal ω) := by
      have hh := (hin z ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.1
      simpa only [Real.coe_toNNReal _ hs.1] using hh
    have hq : ((c (q z)).Q 0 ω).2 = 0 := by rw [(c (q z)).initial ω, hq0 z]
    have hh := log_loewner_height_clock_bounds (τ (z,ω)).coe_nonneg hε hq hd ha
    simpa only [(c (q z)).initial ω] using hh
  have hτlt (z : Z) (ω : Ω) : τ (z,ω) < T := by
    by_contra hn
    have he : τ (z,ω) = T := le_antisymm (hb (z,ω)) (not_lt.mp hn)
    have hh := (hg z ω).2.2.trans (hin z ω (τ (z,ω)) le_rfl).1
    rw [he] at hh
    exact (not_le_of_gt (hT z)) hh
  have he (z : Z) (ω : Ω) :
      logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) = u ∨
      logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) = ε := by
    obtain ⟨hr, ha, hl, hh⟩ := hin z ω (τ (z,ω)) le_rfl
    have hstrictlo : lo < ((c (q z)).Q (τ (z,ω)) ω).1.im := by
      have hdiv := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * ε by positivity)
      linarith [(hg z ω).2.1, hlo z]
    have hstricthi : ((c (q z)).Q (τ (z,ω)) ω).1.im < hi := (hg z ω).1.trans_lt (hhi z)
    by_contra hn
    push Not at hn
    have hp : 0 < D (τ (z,ω)) (z,ω) :=
      by simpa only [D, lt_min_iff, sub_pos] using
        (show logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) < u ∧
          ε < logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) ∧
          lo < ((c (q z)).Q (τ (z,ω)) ω).1.im ∧
          ((c (q z)).Q (τ (z,ω)) ω).1.im < hi from
          ⟨lt_of_le_of_ne hr hn.1, lt_of_le_of_ne ha (Ne.symm hn.2), hstrictlo, hstricthi⟩)
    rw [hzero (z,ω) (hτlt z ω)] at hp
    exact lt_irrefl 0 hp
  refine ⟨τ, hτ, hτlt, hin, ?_, he⟩
  intro z ω t ht
  simpa only [D, lt_min_iff, sub_pos] using hltD (z,ω) t ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure SpatialAngularFamily {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ : ℝ) (z : Z → ℂ) (u ε : ℝ) where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi
  c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi le q
  T : ℝ≥0
  τ : Z × Ω → ℝ≥0
  stopping : IsStoppingTime (spatialFiltration (Z := Z)
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable)))
    (fun p => (τ p : WithTop ℝ≥0))
  bounded : ∀ p, τ p ≤ T
  inside : ∀ x ω t, t ≤ τ (x,ω) →
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q t ω) ≤ u ∧
    ε ≤ logAngleSq κ ((c (initialLogCoordinates (z x))).Q t ω) (B t ω) ∧
    lo ≤ ((c (initialLogCoordinates (z x))).Q t ω).1.im ∧
      ((c (initialLogCoordinates (z x))).Q t ω).1.im ≤ hi
  before : ∀ x ω t, t < τ (x,ω) →
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q t ω) < u ∧
    ε < logAngleSq κ ((c (initialLogCoordinates (z x))).Q t ω) (B t ω)
  boundary : ∀ x ω,
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q (τ (x,ω)) ω) = u ∨
    logAngleSq κ ((c (initialLogCoordinates (z x))).Q (τ (x,ω)) ω) (B (τ (x,ω)) ω) = ε

noncomputable def SpatialAngularFamily.section
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u ε : ℝ}
    (a : SpatialAngularFamily B hm κ z u ε) (x : Z) :
    AngularLocalization B hm κ (z x) u ε where
  lo := a.lo
  hi := a.hi
  le := a.le
  solution := a.c (initialLogCoordinates (z x))
  T := a.T
  τ := fun ω => a.τ (x,ω)
  stopping := spatial_stopping_section a.stopping x
  bounded := fun ω => a.bounded (x,ω)
  inside := a.inside x
  before := a.before x
  boundary := a.boundary x

lemma exists_spatial_angular_family
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (z : Z → ℂ) (hz : Measurable z)
    (l h : ℝ) (hlh : l ≤ h)
    (hη : ∀ x, l ≤ Real.log (z x).im ∧ Real.log (z x).im ≤ h)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hangle : ∀ x, ε ≤ logAngleSq κ (initialLogCoordinates (z x)) 0) :
    Nonempty (SpatialAngularFamily B hm κ z u ε) := by
  classical
  let lo := l - u / (2 * ε) - 1
  let hi := h + 1
  have hud : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  let c (q : ℂ × ℝ) : ClippedLogSolution B hm κ lo hi hle q :=
    (exists_clippedLogSolution B hm hBm hBc κ lo hi hle q).some
  let v := 4 * ε ^ 2 / Real.exp (2 * h)
  have hv : 0 < v := by dsimp [v]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / v)
  have hT : ∀ x, u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates (z x)).1.im)) * ((N : ℝ≥0) : ℝ) := by
    intro x
    have huv := (div_lt_iff₀ hv).mp hN
    have he : Real.exp (2 * Real.log (z x).im) ≤ Real.exp (2 * h) :=
      Real.exp_le_exp.mpr (by linarith [(hη x).2])
    have hd : v ≤ 4 * ε ^ 2 / Real.exp (2 * Real.log (z x).im) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) he
    rw [initialLogCoordinates_im, NNReal.coe_natCast]
    have huv' : u < v * (N : ℝ) := by simpa only [mul_comm (N : ℝ) v] using huv
    exact huv'.trans_le (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg N))
  have hq : Measurable (fun x => initialLogCoordinates (z x)) :=
    measurable_initialLogCoordinates.comp hz
  obtain ⟨τ, hτ, hb, hin, hbefore, hboundary⟩ := spatial_angular_cutoff hm hBc hB0 κ lo hi hle c
    (fun x => initialLogCoordinates (z x)) hq (fun x => rfl) u ε hu hε hangle
    (fun x => by rw [initialLogCoordinates_im]; dsimp [lo]; linarith [(hη x).1])
    (fun x => by rw [initialLogCoordinates_im]; dsimp [hi]; linarith [(hη x).2]) (N : ℝ≥0) hT
  refine ⟨⟨lo, hi, hle, c, N, τ, hτ, fun p => (hb p.1 p.2).le, ?_, ?_, ?_⟩⟩
  · simpa only [initialLogCoordinates_im] using hin
  · intro x ω t ht
    constructor
    · simpa only [initialLogCoordinates_im] using (hbefore x ω t ht).1
    · exact (hbefore x ω t ht).2.1
  · simpa only [initialLogCoordinates_im] using hboundary

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma clipped_area_window_measurable
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ν : Measure Z) [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (σ τ : Z × Ω → ℝ≥0) (hσ : Measurable σ) (hτ : Measurable τ) (T : ℝ≥0) :
    Measurable (fun ω => ∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) ∧
    Measurable (fun ω => ∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) := by
  classical
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hQm := clipped_family_joint_measurable c
  have hD (η : Z × Ω → ℝ≥0) (hη : Measurable η) : Measurable (fun p : Z × Ω =>
      greenLogDensity κ ((c (q p.1)).Q (η p) p.2) (B (η p) p.2)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp
      ((hQm.comp (hη.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
        (hBm.comp (hη.prodMk measurable_snd)))
  refine ⟨((hD τ hτ).sub (hD σ hσ)).stronglyMeasurable.integral_prod_left'.measurable, ?_⟩
  let f (p : ℝ × (Z × Ω)) := if (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ) then
    greenLogCoefficient κ ((c (q p.2.1)).Q p.1 p.2.2) (B p.1.toNNReal p.2.2) else 0
  have hgood : MeasurableSet {p : ℝ × (Z × Ω) | (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ)} :=
    (measurableSet_le (NNReal.continuous_coe.measurable.comp (hσ.comp measurable_snd)) measurable_fst).inter
      (measurableSet_lt measurable_fst (NNReal.continuous_coe.measurable.comp (hτ.comp measurable_snd)))
  have hQreal : Measurable (fun p : ℝ × (Z × Ω) => (c (q p.2.1)).Q p.1.toNNReal p.2.2) :=
    hQm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((hq.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))
  have hcoef : Measurable (fun p : (ℂ × ℝ) × ℝ => greenLogCoefficient κ p.1 p.2) := by
    unfold greenLogCoefficient greenLogNormSq
    apply (greenLogDensity_contDiff κ).continuous.measurable.mul
    fun_prop
  have hfm' : Measurable (fun p : ℝ × (Z × Ω) =>
      if (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ) then
        greenLogCoefficient κ ((c (q p.2.1)).Q p.1.toNNReal p.2.2) (B p.1.toNNReal p.2.2) else 0) := (hcoef.comp
    (hQreal.prodMk (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))))).ite hgood (measurable_const (a := (0 : ℝ)))
  have hfm : Measurable f := by
    convert hfm' using 1
    ext p
    dsimp only [f]
    split_ifs with hp
    · rw [Real.coe_toNNReal _ ((σ p.2).coe_nonneg.trans hp.1)]
    · rfl
  have hswap : Measurable (fun p : Z × (ℝ × Ω) => f (p.2.1,(p.1,p.2.2))) := hfm.comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have harea : Measurable (fun p : ℝ × Ω => ∫ z, f (p.1,(z,p.2)) ∂ν) :=
    hswap.stronglyMeasurable.integral_prod_left'.measurable
  have hh := (harea.pow_const 2).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) T))
  simpa only [intervalIntegral.integral_of_le T.coe_nonneg, f] using hh.measurable

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatial_stopping_lift {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ) :
    IsStoppingTime (spatialFiltration (Z := Z) f) (fun p => τ p.2) := by
  intro t
  let : MeasurableSpace Ω := f t
  exact (hτ t).preimage (measurable_snd : @Measurable (Z × Ω) Ω (mZ.prod (f t)) (f t) Prod.snd)

 

theorem exists_common_brownian_compact_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) (T : ℝ≥0) :
    ∃ π : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (π n ω : WithTop ℝ≥0))) ∧
      (∀ n ω, π n ω ≤ T) ∧
      (∀ n ω t, t ≤ π n ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ n in atTop, π n ω = T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hDa (n : ℕ) : Adapted f (fun t ω => (n : ℝ) + 1 - |B t ω|) := by
    intro t
    have ha := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := f t
    exact measurable_const.sub ha.abs
  have hb (n : ℕ) := first_margin_stopping f (fun t ω => (n : ℝ) + 1 - |B t ω|)
    (hDa n) (fun ω => continuous_const.sub (hBc ω).abs)
    (fun ω => by rw [hB0 ω, abs_zero, sub_zero]; positivity) T
  choose π hπ hb hin hpre hat using hb
  refine ⟨π, hπ, hb, fun n ω t ht => (sub_nonneg.mp (hin n ω t ht)), ?_⟩
  intro ω
  obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
  filter_upwards [eventually_ge_atTop N] with n hn
  apply le_antisymm (hb n ω)
  by_contra h
  have he := hat n ω (not_le.mp h)
  have hh := hN (π n ω) (hb n ω)
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  linarith

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem clipped_spatial_green_window_unbounded_driver
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0)
    (κ lo hi : ℝ) (hle : lo ≤ hi) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (M : ℝ) (hqbound : ∀ z, ‖q z‖ ≤ M) (T : ℝ≥0)
    (σ τ : Z × Ω → ℝ≥0)
    (hσ : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (σ p : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (τ p : WithTop ℝ≥0)))
    (hστ : ∀ p, σ p ≤ τ p) (hτb : ∀ p, τ p ≤ T)
    (hinside : ∀ z ω t, t ≤ τ (z,ω) →
      lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  classical
  obtain ⟨π, hπ, hπb, hπin, hπlim⟩ := exists_common_brownian_compact_stops hm hBc hB0 T
  obtain ⟨L, hL⟩ := clipped_family_uniform_bound c
  let σn (n : ℕ) (p : Z × Ω) := min (σ p) (π n p.2)
  let τn (n : ℕ) (p : Z × Ω) := min (τ p) (π n p.2)
  have hσn (n : ℕ) : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (σn n p : WithTop ℝ≥0)) := by
    simpa only [σn, WithTop.coe_min] using hσ.min (spatial_stopping_lift (Z := Z) (hπ n))
  have hτn (n : ℕ) : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (τn n p : WithTop ℝ≥0)) := by
    simpa only [τn, WithTop.coe_min] using hτ.min (spatial_stopping_lift (Z := Z) (hπ n))
  have hstn (n : ℕ) (p : Z × Ω) : σn n p ≤ τn n p := min_le_min (hστ p) le_rfl
  have htn (n : ℕ) (p : Z × Ω) : τn n p ≤ T := (min_le_left _ _).trans (hτb p)
  let R (n : ℕ) := max M 0 + (L : ℝ) * T + ((n : ℝ) + 1)
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hin (n : ℕ) (z : Z) (ω : Ω) (t : ℝ≥0) (ht : t ≤ τn n (z,ω)) :
      ‖((c (q z)).Q t ω, B t ω)‖ ≤ R n ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi := by
    have htτ := ht.trans (min_le_left _ _)
    have htb := ht.trans (htn n (z,ω))
    refine ⟨?_, hinside z ω t htτ⟩
    rw [Prod.norm_def, max_le_iff]
    have hqt := hL (q z) ω t
    have hmul : (L : ℝ) * t ≤ (L : ℝ) * T := mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr htb) L.coe_nonneg
    have hbm := hπin n ω t (ht.trans (min_le_right _ _))
    have hml : M ≤ max M 0 := le_max_left _ _
    have hmn : 0 ≤ max M 0 := le_max_right _ _
    have hlt : 0 ≤ (L : ℝ) * T := mul_nonneg L.coe_nonneg T.coe_nonneg
    dsimp only [R]
    exact ⟨by linarith [hqbound z, Nat.cast_nonneg (α := ℝ) n], by simpa only [Real.norm_eq_abs] using
      (show |B t ω| ≤ max M 0 + (L : ℝ) * T + ((n : ℝ) + 1) by linarith)⟩
  let X (η ξ : Z × Ω → ℝ≥0) (ω : Ω) :=
    ∫ z, greenLogDensity κ ((c (q z)).Q (ξ (z,ω)) ω) (B (ξ (z,ω)) ω) -
      greenLogDensity κ ((c (q z)).Q (η (z,ω)) ω) (B (η (z,ω)) ω) ∂ν
  let E (η ξ : Z × Ω → ℝ≥0) (ω : Ω) := ∫ t in (0 : ℝ)..(T : ℝ),
    (∫ z, if (η (z,ω) : ℝ) ≤ t ∧ t < (ξ (z,ω) : ℝ) then
      greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2
  have hxm (n : ℕ) := clipped_area_window_measurable ν hBc c q hq (σn n) (τn n)
    (stopping_time_measurable_nnreal (hσn n)) (stopping_time_measurable_nnreal (hτn n)) T
  have hexp (n : ℕ) := clipped_spatial_green_window_exponential (ν := ν) hm hB hBc
    κ lo hi hle hκ hκ8 c q hq (R n) (hR n) T (σn n) (τn n)
      (stopping_time_measurable_nnreal (hσn n)) (stopping_time_measurable_nnreal (hτn n)) (hstn n)
      (stopping_before_measurable (hσn n)) (spatial_stopping_section (hσn n))
      (stopping_before_measurable (hτn n)) (spatial_stopping_section (hτn n))
      (fun z ω => htn n (z,ω)) (hin n) θ
  have hev (ω : Ω) : ∀ᶠ n in atTop,
      X (σn n) (τn n) ω = X σ τ ω ∧ E (σn n) (τn n) ω = E σ τ ω := by
    filter_upwards [hπlim ω] with n hn
    have hs (z : Z) : σn n (z,ω) = σ (z,ω) := by
      dsimp only [σn]; rw [hn, min_eq_left ((hστ (z,ω)).trans (hτb (z,ω))) ]
    have ht (z : Z) : τn n (z,ω) = τ (z,ω) := by
      dsimp only [τn]; rw [hn, min_eq_left (hτb (z,ω))]
    simp only [X, E, hs, ht, and_self]
  apply compensated_exponential_limit_energy
    (fun n => X (σn n) (τn n)) (fun n => E (σn n) (τn n)) (X σ τ) (E σ τ) θ
  · intro n
    exact ((((hxm n).1.const_mul θ).sub (((hxm n).2.const_mul (θ^2)).div_const 2)).exp).ennreal_ofReal.aemeasurable
  · apply Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr' ((hev ω).mono fun n hn => hn.1.symm)
  · apply Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr' ((hev ω).mono fun n hn => hn.2.symm)
  · exact hexp

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal
namespace SLEExactGauge

lemma interval_square_energy_bound (f : ℝ → ℝ) (T : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hb : (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal ((f t)^2)) ≤ ENNReal.ofReal V) :
    (∫ t in (0 : ℝ)..(T : ℝ), (f t)^2) ≤ V := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  have hnorm := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ)))
    (fun t => (f t)^2)
  simp_rw [Real.enorm_eq_ofReal (sq_nonneg _)] at hnorm
  have hi : 0 ≤ ∫ t in Ioc (0 : ℝ) (T : ℝ), (f t)^2 := integral_nonneg (fun t => sq_nonneg _)
  rw [Real.enorm_eq_ofReal hi] at hnorm
  apply (ENNReal.ofReal_le_ofReal_iff hV).mp
  apply hnorm.trans
  apply le_trans _ hb
  exact lintegral_mono_set (fun t ht => ht.1.le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def slabVariance (κ ε r : ℝ) (A : Set ℂ) : ℝ :=
  (ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
    (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A))).toReal

lemma slabVariance_nonneg (κ ε r : ℝ) (A : Set ℂ) : 0 ≤ slabVariance κ ε r A :=
  ENNReal.toReal_nonneg

lemma ofReal_slabVariance (κ ε r : ℝ) (A : Set ℂ) (hfin : volume A ≠ ∞) :
    ENNReal.ofReal (slabVariance κ ε r A) =
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  apply ENNReal.ofReal_toReal
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem localized_spatial_slab_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u δ : ℝ) (b : SpatialAngularFamily a.B a.measurable_B κ
      (Subtype.val : A → ℂ) u δ)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  classical
  let ν := volume.comap (Subtype.val : A → ℂ)
  let σ (p : A × a.samples) := min (boundedSpatialHit (γ p.2) p.1 r S) (b.τ p)
  let τ (p : A × a.samples) := min (boundedSpatialHit (γ p.2) p.1 ε S) (b.τ p)
  have hσ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (σ p : WithTop ℝ≥0)) := by
    simpa only [σ, WithTop.coe_min] using
      (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe r S).min b.stopping
  have hτ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (τ p : WithTop ℝ≥0)) := by
    simpa only [τ, WithTop.coe_min] using
      (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe ε S).min b.stopping
  have hστ (p : A × a.samples) : σ p ≤ τ p := by
    apply min_le_min _ le_rfl
    apply boundedSpatialHit_antitone_radius (a.trace_continuous p.2) p.1 hεr
    rw [(a.witness p.2).2.1, dist_zero_left]
    exact (hheight p.1 p.1.2).trans ((le_abs_self p.1.val.im).trans (Complex.abs_im_le_norm p.1))
  have htbound (p : A × a.samples) : τ p ≤ b.T := (min_le_right _ _).trans (b.bounded p)
  have hin (z : A) (ω : a.samples) (t : ℝ≥0) (ht : t ≤ τ (z,ω)) :
      b.lo ≤ ((b.c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((b.c (initialLogCoordinates z)).Q t ω).1.im ≤ b.hi :=
    (b.inside z ω t (ht.trans (min_le_right _ _))).2.2
  have hexp := clipped_spatial_green_window_unbounded_driver (ν := ν) a.measurable_B a.brownian
    a.continuous_B a.zero_B κ b.lo b.hi b.le hκ (by linarith) b.c
    (fun z : A => initialLogCoordinates z) (measurable_initialLogCoordinates.comp measurable_subtype_coe)
    M hM b.T σ τ hσ hτ hστ htbound hin θ
  let E (ω : a.samples) := ∫ t in (0 : ℝ)..(b.T : ℝ),
    (∫ z : A, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
      greenLogCoefficient κ ((b.c (initialLogCoordinates z)).Q t ω) (a.B t.toNNReal ω) else 0 ∂ν)^2
  have hE (ω : a.samples) : E ω ≤ slabVariance κ ε r A := by
    apply interval_square_energy_bound _ b.T _ (slabVariance_nonneg _ _ _ _)
    rw [ofReal_slabVariance _ _ _ _ hfin]
    apply (a.witness ω).spatial_masked_bracket_bound ((a.continuous_B ω).const_mul _)
      hκ hκ4 hε (hε.trans_le hεr) A hA (fun z hz => hεr.trans (hheight z hz))
    intro t ht z
    have hb := clipped_spatial_window_coefficient_le b.c a.continuous_B z
      (show z.val ∈ upperHalfPlane from hε.trans_le (hεr.trans (hheight z z.2))) ω (b.τ (z,ω)) S
      (γ ω) (a.G ω) (a.F ω) (a.witness ω)
      (fun s hs => (b.inside z ω s hs).2.2) r ε t.toNNReal
    simpa only [σ, τ, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht] using hb
  apply le_trans _ hexp
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  change θ * _ - θ^2 * slabVariance κ ε r A / 2 ≤ θ * _ - θ^2 * E ω / 2
  have hid : (∫ z : A,
      (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
      (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω ∂ν) =
      ∫ z : A, greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (τ (z,ω)) ω) (a.B (τ (z,ω)) ω) -
        greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (σ (z,ω)) ω) (a.B (σ (z,ω)) ω) ∂ν := by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [AngularLocalization.physicalWeight,
      SpatialAngularFamily.section, σ, τ, NNReal.coe_min]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left (hE ω) (sq_nonneg θ)]

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace SpatialAngularFamily
variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u δ : ℝ}

end SpatialAngularFamily
end SLEExactGauge
end
end
end
end
end

end OAI
