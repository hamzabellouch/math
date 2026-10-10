import Mathlib
import OAI.Probability.ParisiFinite.CanonicalSpatialTest

namespace OAI

/-! Measure Coefficient On Support Gap. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

lemma measureCoefficient_on_support_gap
    (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0) {a b : OrderPoint}
    (hgap : ∀ x ∈ Ioo a b, x ∉ (ρ : Measure OrderPoint).support)
    {r : ℝ≥0} (har : (a : ℝ) ≤ r) (hrb : (r : ℝ) < b) :
    measureCoefficient ρ β r = Real.toNNReal ((ρ : Measure OrderPoint).real (Iic a)) * β := by
  unfold measureCoefficient Measure.real
  rw [ParisiGapGeometry.cdf_constant_on_gap _ hgap har hrb]

lemma measureCoefficient_on_support_gap_pos
    (ρ : ProbabilityMeasure OrderPoint) {β : ℝ≥0} (hβ : 0 < β) {a b : OrderPoint}
    (ha : a ∈ (ρ : Measure OrderPoint).support) (hab : a < b)
    (hgap : ∀ x ∈ Ioo a b, x ∉ (ρ : Measure OrderPoint).support) :
    0 < Real.toNNReal ((ρ : Measure OrderPoint).real (Iic a)) * β := by
  apply mul_pos _ hβ
  apply Real.toNNReal_pos.mpr
  exact ENNReal.toReal_pos (ne_of_gt (ParisiGapGeometry.cdf_pos_at_gap_left _ ha hab hgap))
    (measure_ne_top _ _)

 

theorem minimizingParisi_gap_of_not_full_support
    {β : ℝ≥0} (hβ : 0 < β) {ρ : ProbabilityMeasure OrderPoint}
    (hρ : IsMinimizingParisiMeasure β ρ) {q : OrderPoint}
    (hq : q ∈ (ρ : Measure OrderPoint).support)
    (hmax : ∀ t ∈ (ρ : Measure OrderPoint).support, t ≤ q)
    (hne : (ρ : Measure OrderPoint).support ≠ Iic q) :
    ∃ (a b : OrderPoint) (α : ℝ≥0),
      a ∈ (ρ : Measure OrderPoint).support ∧
      b ∈ (ρ : Measure OrderPoint).support ∧
      a < b ∧ b ≤ q ∧ 0 < α ∧
      (∀ x ∈ Ioo a b, x ∉ (ρ : Measure OrderPoint).support) ∧
      ∀ r : ℝ≥0, (a : ℝ) ≤ r → (r : ℝ) < b → measureCoefficient ρ β r = α := by
  obtain ⟨a, b, ha, hb, hab, hbq, hg⟩ :=
    ParisiGapGeometry.support_gap_endpoints (ρ : Measure OrderPoint)
      (minimizingParisi_zero_in_support hβ hρ) hq hmax hne
  refine ⟨a, b, _, ha, hb, hab, hbq,
    measureCoefficient_on_support_gap_pos ρ hβ ha hab hg, hg, ?_⟩
  exact fun r har hrb => measureCoefficient_on_support_gap ρ β hg har hrb

 

lemma dyadicSchedule_congr_on_Ico {γ δ : ℝ≥0 → ℝ≥0} {a b : ℝ≥0}
    (h : Set.EqOn γ δ (Ico a b)) (t d : ℝ≥0) (ha : a ≤ t)
    (hd : 0 < d) (ht : t + d ≤ b) (n : ℕ) :
    dyadicSchedule γ false t d n = dyadicSchedule δ false t d n := by
  induction n generalizing t d with
  | zero =>
    simp only [dyadicSchedule, Bool.false_eq_true, ↓reduceIte]
    rw [h ⟨ha, lt_of_lt_of_le (lt_add_of_pos_right t hd) ht⟩]
  | succ n ih =>
    simp only [dyadicSchedule]
    rw [ih t (d/2) ha (by positivity) (by nlinarith),
      ih (t+d/2) (d/2) (by nlinarith) (by positivity) (by nlinarith)]

 

lemma field_on_plateau (β : ℝ≥0) (hβ : 0 < β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s, γ s ≤ β) {a b α : ℝ≥0}
    (hb1 : b ≤ 1) (hg : ∀ s ∈ Ico a b, γ s = α)
    {t : ℝ≥0} (ht : t ∈ Ico a b) (x : ℝ) :
    field β γ t x = step α (Real.sqrt (b-t)) (field β γ b) x := by
  rw [field_DPP β hβ hγ hb ht.2.le hb1]
  have he : dyadicEvolution γ t (b-t) (field β γ b) x =
      dyadicEvolution (fun _ => α) t (b-t) (field β γ b) x := by
    unfold dyadicEvolution
    apply congrArg sSup
    apply congrArg Set.range
    funext n
    rw [dyadicSchedule_congr_on_Ico (show Set.EqOn γ (fun _ => α) (Ico a b) from hg)
      t (b-t) ht.1 (tsub_pos_iff_lt.mpr ht.2)
      (by rw [add_tsub_cancel_of_le ht.2.le]) n]
  rw [he, dyadicEvolution_constant (field_lipschitz β hβ hγ hb b) α t (b-t) x,
    NNReal.coe_sub ht.2.le]

 

def canonicalSmoothField (β : ℝ≥0) (hβ : 0 < β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s, γ s ≤ β) (t : ℝ≥0) : SmoothField where
  val := field β γ t
  d1 := fieldGradient β γ t
  d2 := fieldCurvature β γ t
  hasD1 := hasDerivAt_field β hβ hγ hb t
  hasD2 := hasDerivAt_fieldGradient β hβ hγ hb t
  continuousD2 := (fieldCurvature_lipschitz β hβ hγ hb t).continuous
  bound1 := 1
  bound2 := β
  normD1 := fieldGradient_bound β hβ hγ hb t
  normD2 := fieldCurvature_abs β hβ hγ hb t

lemma fieldGradient_on_plateau (β : ℝ≥0) (hβ : 0 < β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s, γ s ≤ β) {a b α : ℝ≥0}
    (hb1 : b ≤ 1) (hg : ∀ s ∈ Ico a b, γ s = α)
    {t : ℝ≥0} (ht : t ∈ Ico a b) (x : ℝ) :
    fieldGradient β γ t x =
      tiltedMean α (Real.sqrt (b-t)) (field β γ b) (fieldGradient β γ b) x := by
  have he : field β γ t = step α (Real.sqrt (b-t)) (field β γ b) :=
    funext (field_on_plateau β hβ hγ hb hb1 hg ht)
  apply (hasDerivAt_field β hβ hγ hb t x).unique
  rw [he]
  exact hasDerivAt_step (canonicalSmoothField β hβ hγ hb b) α (Real.sqrt (b-t)) x

 

lemma fieldCurvature_on_plateau (β : ℝ≥0) (hβ : 0 < β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ s, γ s ≤ β) {a b α : ℝ≥0}
    (hb1 : b ≤ 1) (hg : ∀ s ∈ Ico a b, γ s = α)
    {t : ℝ≥0} (ht : t ∈ Ico a b) (x : ℝ) :
    fieldCurvature β γ t x =
      tiltedMean α (Real.sqrt (b-t)) (field β γ b) (fieldCurvature β γ b) x +
      (α : ℝ) * (tiltedMean α (Real.sqrt (b-t)) (field β γ b)
        (fun y => (fieldGradient β γ b y)^2) x - (fieldGradient β γ t x)^2) := by
  have he : fieldGradient β γ t =
      tiltedMean α (Real.sqrt (b-t)) (field β γ b) (fieldGradient β γ b) :=
    funext (fieldGradient_on_plateau β hβ hγ hb hb1 hg ht)
  rw [congrFun he x]
  apply (hasDerivAt_fieldGradient β hβ hγ hb t x).unique
  rw [he]
  exact hasDerivAt_tiltedMean_d1 (canonicalSmoothField β hβ hγ hb b)
    α (Real.sqrt (b-t)) x

 

lemma fieldGradient_tilted_variance_pos (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ r, γ r ≤ β)
    (t : ℝ≥0) (α x : ℝ) {s : ℝ} (hs : s ≠ 0) :
    0 < tiltedMean α s (field β γ t) (fun y => (fieldGradient β γ t y)^2) x -
      (tiltedMean α s (field β γ t) (fieldGradient β γ t) x)^2 := by
  let f := canonicalSmoothField β hβ hγ hb t
  let μ := transitionMeasure f α s x
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  let : Measure.IsOpenPosMeasure ((gaussianReal 0 1).tilted
      (fun z => α*f.val (x+s*z))) :=
    (absolutelyContinuous_tilted (integrable_exp_shift f.lipschitz α x s)).isOpenPosMeasure
  have hsur : Function.Surjective (fun z : ℝ => x+s*z) := by
    intro y
    refine ⟨(y-x)/s, ?_⟩
    field_simp
    ring
  let : Measure.IsOpenPosMeasure μ :=
    (show Continuous (fun z : ℝ => x+s*z) by fun_prop).isOpenPosMeasure_map hsur
  have hm : MemLp f.d1 2 μ := MemLp.of_bound f.continuousD1.aestronglyMeasurable 1
    (ae_of_all _ fun y => f.normD1 y)
  have hv : 0 < variance f.d1 μ := by
    apply lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm ?_)
    intro hz
    have hae := ae_eq_integral_of_variance_eq_zero hm hz
    have he := Measure.eq_of_ae_eq hae f.continuousD1 continuous_const
    have hd := f.hasD2 0
    rw [he] at hd
    have hz2 := hd.unique (hasDerivAt_const 0 (∫ y, f.d1 y ∂μ))
    exact (fieldCurvature_bounds β hβ hγ hb t 0).1.ne' hz2
  rw [variance_eq_sub hm] at hv
  change 0 < (∫ y, f.d1 y ^ 2 ∂transitionMeasure f α s x) -
    (∫ y, f.d1 y ∂transitionMeasure f α s x)^2 at hv
  rw [transition_integral f α s x (g := fun y => f.d1 y ^ 2)
    (show Measurable (fun y => f.d1 y ^ 2) from (f.continuousD1.pow 2).measurable),
    transition_integral f α s x f.continuousD1.measurable] at hv
  exact hv

 

lemma fieldCurvature_gt_tilted_mean_on_plateau (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ r, γ r ≤ β)
    {a b α : ℝ≥0} (hb1 : b ≤ 1) (hα : 0 < α)
    (hg : ∀ r ∈ Ico a b, γ r = α) {t : ℝ≥0} (ht : t ∈ Ico a b) (x : ℝ) :
    tiltedMean α (Real.sqrt (b-t)) (field β γ b) (fieldCurvature β γ b) x <
      fieldCurvature β γ t x := by
  rw [fieldCurvature_on_plateau β hβ hγ hb hb1 hg ht,
    fieldGradient_on_plateau β hβ hγ hb hb1 hg ht]
  apply lt_add_of_pos_right
  apply mul_pos (show (0 : ℝ) < α from hα)
  exact fieldGradient_tilted_variance_pos β hβ hγ hb b α x
    (Real.sqrt_pos.mpr (sub_pos.mpr (show (t : ℝ) < b from ht.2))).ne'

section GapContact
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

 

lemma minimizingParisi_squareCurvature_integral_between_support
    (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {a b : OrderPoint} (ha : a ∈ (ρ : Measure OrderPoint).support)
    (hb : b ∈ (ρ : Measure OrderPoint).support) (hab : a ≤ b) :
    (∫ t in (a : ℝ)..(b : ℝ), (ofMeasure β ρ).expectedSquareCurvature P W hβ t) =
      (b : ℝ) - (a : ℝ) := by
  let c := ofMeasure β ρ
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (a : ℝ) ≤ (b : ℝ) from hab)
    (expectedProduct_continuous hW c c hβ (c.driftData hβ)).continuousOn
    (fun t ht => hasDerivAt_expectedProduct_self hW hβ c t
      ⟨lt_of_le_of_lt a.property.1 ht.1, lt_of_lt_of_le ht.2 b.property.2⟩)
    ((c.expectedSquareCurvature_continuous hW hβ).intervalIntegrable _ _)
  rw [minimizingParisi_selfConsistency hW hβ hρ ha,
    minimizingParisi_selfConsistency hW hβ hρ hb] at he
  exact he

 
lemma minimizingParisi_deviation_integral_between_support
    (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {a b : OrderPoint} (ha : a ∈ (ρ : Measure OrderPoint).support)
    (hb : b ∈ (ρ : Measure OrderPoint).support) :
    (∫ t in (a : ℝ)..(b : ℝ), deviation P W hβ (ofMeasure β ρ) t) = 0 := by
  have he := le_antisymm (minimizingParisi_support_potential hW hβ hρ ha b)
    (minimizingParisi_support_potential hW hβ hρ hb a)
  have hc := continuous_deviation hW hβ (ofMeasure β ρ)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a : ℝ) b)
    (hc.intervalIntegrable (μ := volume) (b : ℝ) 1)
  unfold variationalPotential at he
  linarith

 

lemma minimizingParisi_deviation_integral_le_zero
    (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {a : OrderPoint} (ha : a ∈ (ρ : Measure OrderPoint).support) (t : OrderPoint) :
    (∫ s in (a : ℝ)..(t : ℝ), deviation P W hβ (ofMeasure β ρ) s) ≤ 0 := by
  have he := minimizingParisi_support_potential hW hβ hρ ha t
  have hc := continuous_deviation hW hβ (ofMeasure β ρ)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a : ℝ) t)
    (hc.intervalIntegrable (μ := volume) (t : ℝ) 1)
  unfold variationalPotential at he
  linarith

 

lemma minimizingParisi_replicon_zero (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    (hz : (⟨0, by simp⟩ : OrderPoint) ∈ (ρ : Measure OrderPoint).support) :
    (ofMeasure β ρ).expectedSquareCurvature P W hβ 0 ≤ 1 := by
  let c := ofMeasure β ρ
  let f := c.expectedSquareCurvature P W hβ
  let g := deviation P W hβ c
  let G := fun t : ℝ => (∫ s in (0 : ℝ)..t, f s) - t
  have hf : Continuous f := c.expectedSquareCurvature_continuous hW hβ
  have hg : Continuous g := continuous_deviation hW hβ c
  have hG : HasDerivAt G (f 0 - 1) 0 :=
    (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 0)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).sub
      (hasDerivAt_id (0 : ℝ))
  have hG0 : G 0 = 0 := by simp [G]
  have hEq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : g t = G t := by
    change expectedProduct P W c c (c.driftData hβ) t - t = _
    rw [spin_mean_square_evolution hW hβ c t ht]
  by_contra hn
  have hp : 0 < f 0 - 1 := sub_pos.mpr (not_le.mp hn)
  have hs := (hG.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))).eventually
    (lt_mem_nhds hp)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t ∧ t < 1 := by
    filter_upwards [hs, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t hs ht ht1
    refine ⟨?_, ht1⟩
    rw [slope_def_field] at hs
    change 0 < (G t - G 0) / (t - 0) at hs
    rw [hG0, sub_zero, sub_zero] at hs
    rw [hEq t ⟨ht, ht1⟩]
    exact (div_pos_iff_of_pos_right ht).mp hs
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  have hu1 : u < 1 := (hsub ⟨hu, le_rfl⟩).2
  have hi : 0 < ∫ t in (0 : ℝ)..u, g t :=
    intervalIntegral.integral_pos hu hg.continuousOn
      (fun t ht => (hsub ht).1.le) ⟨u, ⟨hu.le, le_rfl⟩, (hsub ⟨hu, le_rfl⟩).1⟩
  have hmin := minimizingParisi_deviation_integral_le_zero hW hβ hρ hz
    ⟨u, hu.le, hu1.le⟩
  exact (not_lt_of_ge hmin) hi

lemma minimizingParisi_replicon_of_lt_one (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t ∈ (ρ : Measure OrderPoint).support) (h1 : (t : ℝ) < 1) :
    (ofMeasure β ρ).expectedSquareCurvature P W hβ t ≤ 1 := by
  by_cases h0 : (t : ℝ) = 0
  · have he : t = (⟨0, by simp⟩ : OrderPoint) := Subtype.ext h0
    subst t
    exact minimizingParisi_replicon_zero hW hβ hρ ht
  · exact minimizingParisi_replicon hW hβ hρ ht
      (lt_of_le_of_ne t.property.1 (Ne.symm h0)) h1

 

theorem minimizingParisi_not_strictConvex_between_support
    (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {a b : OrderPoint} (ha : a ∈ (ρ : Measure OrderPoint).support)
    (hb : b ∈ (ρ : Measure OrderPoint).support) (hab : a < b) (hb1 : (b : ℝ) < 1) :
    ¬ StrictConvexOn ℝ (Icc (a : ℝ) (b : ℝ))
        ((ofMeasure β ρ).expectedSquareCurvature P W hβ) := by
  intro hconv
  let c := ofMeasure β ρ
  let f := c.expectedSquareCurvature P W hβ
  have hab' : (a : ℝ) < b := hab
  have ha1 := minimizingParisi_replicon_of_lt_one hW hβ hρ ha (hab'.trans hb1)
  have hb1' := minimizingParisi_replicon_of_lt_one hW hβ hρ hb hb1
  have hends : max (f a) (f b) ≤ 1 := max_le ha1 hb1'
  have hac : (a : ℝ) ∈ Icc (a : ℝ) (b : ℝ) := ⟨le_rfl, hab'.le⟩
  have hbc : (b : ℝ) ∈ Icc (a : ℝ) (b : ℝ) := ⟨hab'.le, le_rfl⟩
  have hle : ∀ t ∈ Ioc (a : ℝ) (b : ℝ), f t ≤ 1 := by
    intro t ht
    exact (hconv.convexOn.le_on_segment hac hbc (Icc_subset_segment ⟨ht.1.le, ht.2⟩)).trans hends
  have hm : ((a : ℝ) + b) / 2 ∈ Ioo (a : ℝ) (b : ℝ) := by
    constructor <;> linarith
  have hlt : f (((a : ℝ) + b)/2) < 1 :=
    (hconv.lt_on_openSegment hac hbc hab'.ne (Ioo_subset_openSegment hm)).trans_le hends
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab' (c.expectedSquareCurvature_continuous hW hβ).continuousOn
    (continuous_const (y := (1 : ℝ))).continuousOn hle
    ⟨((a : ℝ) + b)/2, Ioo_subset_Icc_self hm, hlt⟩
  rw [minimizingParisi_squareCurvature_integral_between_support hW hβ hρ ha hb hab.le] at hint
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, lt_self_iff_false] at hint

end GapContact

 

theorem minimizingParisi_noGap_countercase {β : ℝ≥0} (hβ : (1 : ℝ) < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    (hne : ¬ ∃ q : OrderPoint, 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧
      (ρ : Measure OrderPoint).support = Iic q) :
    ∃ (hbp : 0 < β) (a b : OrderPoint) (α : ℝ≥0),
      a ∈ (ρ : Measure OrderPoint).support ∧ b ∈ (ρ : Measure OrderPoint).support ∧
      a < b ∧ (b : ℝ) < 1 ∧ 0 < α ∧
      (∀ x ∈ Ioo a b, x ∉ (ρ : Measure OrderPoint).support) ∧
      (∀ r : ℝ≥0, (a : ℝ) ≤ r → (r : ℝ) < b → measureCoefficient ρ β r = α) ∧
      (∫ t in (a : ℝ)..(b : ℝ), (ofMeasure β ρ).expectedSquareCurvature
        BrownianConstruction.brownianMeasure BrownianConstruction.brownianMotion hbp t) =
        (b : ℝ) - (a : ℝ) ∧
      (∫ t in (a : ℝ)..(b : ℝ), deviation BrownianConstruction.brownianMeasure
        BrownianConstruction.brownianMotion hbp (ofMeasure β ρ) t) = 0 ∧
      (∀ t : OrderPoint, (∫ s in (a : ℝ)..(t : ℝ), deviation
        BrownianConstruction.brownianMeasure BrownianConstruction.brownianMotion
        hbp (ofMeasure β ρ) s) ≤ 0) ∧
      ¬ StrictConvexOn ℝ (Icc (a : ℝ) (b : ℝ)) ((ofMeasure β ρ).expectedSquareCurvature
        BrownianConstruction.brownianMeasure BrownianConstruction.brownianMotion hbp) := by
  have hbp : 0 < β := by exact_mod_cast (zero_lt_one.trans hβ)
  obtain ⟨q, hq0, hq1, hq, hmax, _⟩ := minimizingParisi_support_boundary hβ hρ
  have hneq : (ρ : Measure OrderPoint).support ≠ Iic q := fun he => hne ⟨q, hq0, hq1, he⟩
  obtain ⟨a, b, α, ha, hb, hab, hbq, hα, hg, hc⟩ :=
    minimizingParisi_gap_of_not_full_support hbp hρ hq hmax hneq
  have hb1 : (b : ℝ) < 1 := (show (b : ℝ) ≤ q from hbq).trans_lt hq1
  refine ⟨hbp, a, b, α, ha, hb, hab, hb1, hα, hg, hc, ?_, ?_, ?_, ?_⟩
  · exact minimizingParisi_squareCurvature_integral_between_support
      BrownianConstruction.brownianMotion_isBrownian hbp hρ ha hb hab.le
  · exact minimizingParisi_deviation_integral_between_support
      BrownianConstruction.brownianMotion_isBrownian hbp hρ ha hb
  · exact minimizingParisi_deviation_integral_le_zero
      BrownianConstruction.brownianMotion_isBrownian hbp hρ ha
  · exact minimizingParisi_not_strictConvex_between_support
      BrownianConstruction.brownianMotion_isBrownian hbp hρ ha hb hab hb1

end ParisiFinite

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

 
private lemma contact_area_has_interior_localMax {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : Continuous f) (ha : f a ≤ 1) (hb : f b ≤ 1)
    (harea : (∫ t in a..b, f t) = b - a) :
    ∃ t ∈ Ioo a b, 1 ≤ f t ∧ IsLocalMax f t := by
  by_cases hgt : ∃ s ∈ Icc a b, 1 < f s
  · obtain ⟨s, hs, hfs⟩ := hgt
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hab.le) hf.continuousOn
    have hft : 1 < f t := hfs.trans_le (hmax hs)
    have hat : a < t := lt_of_le_of_ne ht.1 (by
      intro he
      subst t
      exact (not_lt_of_ge ha) hft)
    have htb : t < b := lt_of_le_of_ne ht.2 (by
      intro he
      subst t
      exact (not_lt_of_ge hb) hft)
    exact ⟨t, ⟨hat, htb⟩, hft.le, hmax.isLocalMax (Icc_mem_nhds hat htb)⟩
  · have hle : ∀ s ∈ Icc a b, f s ≤ 1 := by
      intro s hs
      exact not_lt.mp (fun h => hgt ⟨s, hs, h⟩)
    let t := (a + b) / 2
    have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
    have hft : 1 ≤ f t := by
      by_contra hn
      have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hab hf.continuousOn (continuous_const (y := (1 : ℝ))).continuousOn
        (fun s hs => hle s (Ioc_subset_Icc_self hs))
        ⟨t, Ioo_subset_Icc_self ht, not_le.mp hn⟩
      rw [harea] at hlt
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
        lt_self_iff_false] at hlt
    refine ⟨t, ht, hft, ?_⟩
    apply IsMaxOn.isLocalMax (s := Icc a b) ?_ (Icc_mem_nhds ht.1 ht.2)
    intro s hs
    exact (hle s hs).trans hft

 

theorem minimizingParisi_localMax_between_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    {β : ℝ≥0} (hW : IsBrownianReal W P) (hβ : 0 < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {a b : OrderPoint} (ha : a ∈ (ρ : Measure OrderPoint).support)
    (hb : b ∈ (ρ : Measure OrderPoint).support) (hab : a < b) (hb1 : (b : ℝ) < 1) :
    ∃ t ∈ Ioo (a : ℝ) (b : ℝ),
      1 ≤ (ofMeasure β ρ).expectedSquareCurvature P W hβ t ∧
      IsLocalMax ((ofMeasure β ρ).expectedSquareCurvature P W hβ) t := by
  exact contact_area_has_interior_localMax hab
    ((ofMeasure β ρ).expectedSquareCurvature_continuous hW hβ)
    (minimizingParisi_replicon_of_lt_one hW hβ hρ ha
      ((show (a : ℝ) < b from hab).trans hb1))
    (minimizingParisi_replicon_of_lt_one hW hβ hρ hb hb1)
    (minimizingParisi_squareCurvature_integral_between_support hW hβ hρ ha hb hab.le)

 

theorem minimizingParisi_positive_plateau_localMax_countercase
    {β : ℝ≥0} (hβ : (1 : ℝ) < β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    (hne : ¬ ∃ q : OrderPoint, 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧
      (ρ : Measure OrderPoint).support = Iic q) :
    ∃ (hbp : 0 < β) (a b : OrderPoint) (α : ℝ≥0) (t : ℝ),
      a ∈ (ρ : Measure OrderPoint).support ∧ b ∈ (ρ : Measure OrderPoint).support ∧
      a < b ∧ (b : ℝ) < 1 ∧ 0 < α ∧
      (∀ x ∈ Ioo a b, x ∉ (ρ : Measure OrderPoint).support) ∧
      (∀ r : ℝ≥0, (a : ℝ) ≤ r → (r : ℝ) < b → measureCoefficient ρ β r = α) ∧
      t ∈ Ioo (a : ℝ) (b : ℝ) ∧
      1 ≤ (ofMeasure β ρ).expectedSquareCurvature
        BrownianConstruction.brownianMeasure BrownianConstruction.brownianMotion hbp t ∧
      IsLocalMax ((ofMeasure β ρ).expectedSquareCurvature
        BrownianConstruction.brownianMeasure BrownianConstruction.brownianMotion hbp) t := by
  obtain ⟨hbp, a, b, α, ha, hb, hab, hb1, hα, hg, hc, _⟩ :=
    minimizingParisi_noGap_countercase hβ hρ hne
  obtain ⟨t, ht, hft, hmax⟩ := minimizingParisi_localMax_between_support
    BrownianConstruction.brownianMotion_isBrownian hbp hρ ha hb hab hb1
  exact ⟨hbp, a, b, α, t, ha, hb, hab, hb1, hα, hg, hc, ht, hft, hmax⟩

end ParisiFinite

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

 

def terminalPerturbation (f g : SmoothField) (u : ℝ) : SmoothField where
  val x := f.val x + Real.sin u*g.val x
  d1 x := f.d1 x + Real.sin u*g.d1 x
  d2 x := f.d2 x + Real.sin u*g.d2 x
  hasD1 x := (f.hasD1 x).add ((g.hasD1 x).const_mul _)
  hasD2 x := (f.hasD2 x).add ((g.hasD2 x).const_mul _)
  continuousD2 := f.continuousD2.add (g.continuousD2.const_mul _)
  bound1 := f.bound1+g.bound1
  bound2 := f.bound2+g.bound2
  normD1 x := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add (f.normD1 x)
      ((mul_le_mul (Real.abs_sin_le_one u) (g.normD1 x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  normD2 x := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add (f.normD2 x)
      ((mul_le_mul (Real.abs_sin_le_one u) (g.normD2 x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))

def SmoothField.directional (f : SmoothField) : DirectionalField ℝ where
  val := f.val
  first v x := v*f.d1 x
  second v w x := v*w*f.d2 x
  lip := f.bound1
  lipschitz := f.lipschitz
  continuousFirst v := f.continuousD1.const_mul v
  continuousSecond v w := f.continuousD2.const_mul (v*w)
  hasFirst v x t := by
    simpa only [smul_eq_mul, Function.comp_def, id_eq, one_mul, mul_one, mul_comm] using
      (f.hasD1 (x+t*v)).comp t ((hasDerivAt_id t).mul_const v |>.const_add x)
  hasSecond v w x t := by
    simpa only [smul_eq_mul, Function.comp_def, id_eq, one_mul, mul_one,
      mul_assoc, mul_comm, mul_left_comm] using
      ((f.hasD2 (x+t*v)).comp t
        ((hasDerivAt_id t).mul_const v |>.const_add x)).const_mul w
  boundFirst v := Real.nnabs v*f.bound1
  boundSecond v w := Real.nnabs v*Real.nnabs w*f.bound2
  normFirst v x := by
    simpa only [abs_mul, NNReal.coe_mul, Real.coe_nnabs] using
      mul_le_mul_of_nonneg_left (f.normD1 x) (abs_nonneg v)
  normSecond v w x := by
    simpa only [abs_mul, NNReal.coe_mul, Real.coe_nnabs, mul_assoc] using
      mul_le_mul_of_nonneg_left (f.normD2 x) (mul_nonneg (abs_nonneg v) (abs_nonneg w))

def terminalFamily (f g : SmoothField) (R : ℝ≥0) (hR : ∀ x, |g.val x|≤R) : FieldFamily ℝ where
  field u := (terminalPerturbation f g u).directional
  dot u x := Real.cos u*g.val x
  continuousVal := by
    change Continuous (fun p : ℝ×ℝ => f.val p.2+Real.sin p.1*g.val p.2)
    exact (f.continuousVal.comp continuous_snd).add
      ((Real.continuous_sin.comp continuous_fst).mul (g.continuousVal.comp continuous_snd))
  continuousFirst v := by
    change Continuous (fun p : ℝ×ℝ => v*(f.d1 p.2+Real.sin p.1*g.d1 p.2))
    have hf := f.continuousD1
    have hg := g.continuousD1
    fun_prop
  continuousSecond v w := by
    change Continuous (fun p : ℝ×ℝ => v*w*(f.d2 p.2+Real.sin p.1*g.d2 p.2))
    have hf := f.continuousD2
    have hg := g.continuousD2
    fun_prop
  continuousDot := (Real.continuous_cos.comp continuous_fst).mul (g.continuousVal.comp continuous_snd)
  hasDot x u := (Real.hasDerivAt_sin u).mul_const (g.val x) |>.const_add (f.val x)
  lip := f.bound1+g.bound1
  lipschitz u := (terminalPerturbation f g u).lipschitz
  boundFirst v := Real.nnabs v*(f.bound1+g.bound1)
  boundSecond v w := Real.nnabs v*Real.nnabs w*(f.bound2+g.bound2)
  boundDot _ := R
  continuousBound := continuous_const
  normFirst u v x := (terminalPerturbation f g u).directional.normFirst v x
  normSecond u v w x := (terminalPerturbation f g u).directional.normSecond v w x
  normDot u x := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one u) (hR x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

 
def evolveFamily (F : FieldFamily ℝ) : Schedule → FieldFamily ℝ
  | [] => F
  | (a,d)::ls => (evolveFamily F ls).transform a 1 (fun _ => Real.sqrt d) (fun _ => 0)
      continuous_const continuous_const (fun u => hasDerivAt_const u _)

lemma ambientStep_real (a s : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ambientStep a s f x = step a s f x := by
  simp only [ambientStep, step, smul_eq_mul, mul_comm s]

lemma ambientTilt_real (a s : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    ambientTilt a s f g x = tiltedMean a s f g x := by
  simp only [ambientTilt, ambientMoment, ambientMass, tiltedMean, expMoment, expMass,
    smul_eq_mul, mul_comm s]

lemma evolveFamily_val (F : FieldFamily ℝ) (ls : Schedule) (u x : ℝ) :
    ((evolveFamily F ls).field u).val x = evolve ls (F.field u).val x := by
  induction ls generalizing x with
  | nil => rfl
  | cons l ls ih =>
    dsimp only [evolveFamily, FieldFamily.transform, DirectionalField.transform]
    simp only [smul_eq_mul, mul_one, ambientStep_real]
    rw [funext ih]
    rfl

 
def linearEvolve (f g : ℝ → ℝ) : Schedule → ℝ → ℝ
  | [] => g
  | (a,d)::ls => tiltedMean a (Real.sqrt d) (evolve ls f) (linearEvolve f g ls)

lemma evolveFamily_dot (F : FieldFamily ℝ) (ls : Schedule) (u x : ℝ) :
    (evolveFamily F ls).dot u x = linearEvolve (F.field u).val (F.dot u) ls x := by
  induction ls generalizing x with
  | nil => rfl
  | cons l ls ih =>
    dsimp only [evolveFamily, FieldFamily.transform, FieldFamily.transformedDot]
    simp only [mul_zero, zero_mul, add_zero, smul_eq_mul, mul_one, ambientTilt_real]
    rw [funext (evolveFamily_val F ls u), funext ih]
    rfl

lemma hasDerivAt_evolve_terminal (f g : SmoothField) (R : ℝ≥0)
    (hR : ∀ x, |g.val x|≤R) (ls : Schedule) (x : ℝ) :
    HasDerivAt (fun u => evolve ls (terminalPerturbation f g u).val x)
      (linearEvolve f.val g.val ls x) 0 := by
  have hh := (evolveFamily (terminalFamily f g R hR) ls).hasDot x 0
  simp_rw [evolveFamily_val, evolveFamily_dot] at hh
  simpa only [terminalFamily, SmoothField.directional, terminalPerturbation,
    Real.sin_zero, Real.cos_zero, zero_mul, add_zero, one_mul] using hh

end ParisiFinite

end

end OAI
