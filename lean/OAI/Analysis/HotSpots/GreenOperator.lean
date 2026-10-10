import OAI.Analysis.HotSpots.Green

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology
namespace StrictHotSpots.DiskFormula

def poisson (s x : ℂ) : ℝ := (1 - ‖x‖ ^ 2) / (2 * Real.pi * ‖s-x‖ ^ 2)

def boundaryInteraction (s t : ℂ) : ℝ := 1 / (Real.pi * ‖s-t‖ ^ 2)

private def logRatio (u : ℝ) : ℝ := dslope Real.log 1 (1+u)

private lemma logRatio_zero : logRatio 0 = 1 := by
  simp [logRatio, Real.deriv_log]

private lemma logRatio_continuousAt_zero : ContinuousAt logRatio 0 := by
  have hd : ContinuousAt (dslope Real.log 1) 1 :=
    continuousAt_dslope_same.mpr (Real.differentiableAt_log one_ne_zero)
  exact hd.comp_of_eq (show ContinuousAt (fun t : ℝ => 1+t) 0 from
    continuousAt_const.add continuousAt_id) (by simp)

private lemma log_eq_mul_ratio (u : ℝ) : Real.log (1+u) = u * logRatio u := by
  have h := sub_smul_dslope Real.log 1 (1+u)
  simpa [logRatio, smul_eq_mul] using h.symm

lemma tendsto_log_mul_div {α : Type*} {l : Filter α} {a b : α → ℝ} {B : ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 B))
    (hne : ∀ᶠ z in l, a z ≠ 0) :
    Tendsto (fun z => Real.log (1 + a z * b z) / a z) l (𝓝 B) := by
  have hu : Tendsto (fun z => a z * b z) l (𝓝 0) := by simpa using ha.mul hb
  have ht := (logRatio_continuousAt_zero.tendsto.comp hu).mul hb
  rw [logRatio_zero, one_mul] at ht
  apply ht.congr'
  filter_upwards [hne] with z hz
  rw [log_eq_mul_ratio]
  dsimp only [Function.comp_def]
  field_simp [hz]

lemma radial_one_formula (s x : ℂ) (hs : ‖s‖ = 1) (r : ℝ) :
    green (r • s) x = Real.log (1 + (1-r^2) * (1-‖x‖^2) / ‖r • s-x‖^2) /
      (4 * Real.pi) := by
  simp only [green, norm_smul, Real.norm_eq_abs, hs, mul_one, sq_abs]

lemma radial_one (s x : ℂ) (hs : ‖s‖ = 1) (hx : ‖x‖ < 1) :
    Tendsto (fun r : ℝ => green (r • s) x / (1-r)) (𝓝[<] 1) (𝓝 (poisson s x)) := by
  have hne : s-x ≠ 0 := by
    intro h
    have he : s = x := sub_eq_zero.mp h
    rw [← he, hs] at hx
    exact lt_irrefl _ hx
  have hden : ‖s-x‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
  have hd : ContinuousAt (fun r : ℝ => ‖r • s-x‖^2) 1 := by fun_prop
  have hb : Tendsto (fun r : ℝ => (1+r)*(1-‖x‖^2)/‖r • s-x‖^2)
      (𝓝[<] 1) (𝓝 (2*(1-‖x‖^2)/‖s-x‖^2)) := by
    have hh : ContinuousAt (fun r : ℝ => (1+r)*(1-‖x‖^2)/‖r • s-x‖^2) 1 :=
      ((continuousAt_const.add continuousAt_id).mul continuousAt_const).div hd
        (by simpa using hden)
    convert hh.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have ha : Tendsto (fun r : ℝ => 1-r) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun r : ℝ => 1-r) (𝓝[<] 1) (𝓝 (1-1)))
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] 1, (1-r) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (sub_pos.mpr hr).ne'
  have ht := (tendsto_log_mul_div ha hb hevent).div_const (4*Real.pi)
  have hv : 2*(1-‖x‖^2)/‖s-x‖^2/(4*Real.pi) = poisson s x := by
    simp only [poisson]
    field_simp
    ring
  rw [hv] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall fun r => by
    dsimp only
    rw [radial_one_formula s x hs]
    have he : (1-r^2)*(1-‖x‖^2)/‖r • s-x‖^2 =
        (1-r)*((1+r)*(1-‖x‖^2)/‖r • s-x‖^2) := by ring
    rw [he]
    ring

lemma radial_two_formula (s t : ℂ) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (r : ℝ) :
    green (r • s) (r • t) =
      Real.log (1 + (1-r^2)^2 / (r^2 * ‖s-t‖^2)) / (4*Real.pi) := by
  simp only [green, ← smul_sub, norm_smul, Real.norm_eq_abs, hs, ht, mul_one,
    mul_pow, sq_abs, ← pow_two]

lemma radial_two (s t : ℂ) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) (hne : s ≠ t) :
    Tendsto (fun r : ℝ => green (r • s) (r • t) / (1-r)^2)
      (𝓝[<] 1) (𝓝 (boundaryInteraction s t)) := by
  have hden : ‖s-t‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  have hb : Tendsto (fun r : ℝ => (1+r)^2 / (r^2 * ‖s-t‖^2))
      (𝓝[<] 1) (𝓝 (4 / ‖s-t‖^2)) := by
    have hh : ContinuousAt (fun r : ℝ => (1+r)^2 / (r^2 * ‖s-t‖^2)) 1 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simpa using hden
    convert hh.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have ha : Tendsto (fun r : ℝ => (1-r)^2) (𝓝[<] 1) (𝓝 0) := by
    have hh : ContinuousAt (fun r : ℝ => (1-r)^2) 1 := by fun_prop
    convert hh.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] 1, (1-r)^2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact pow_ne_zero _ (sub_pos.mpr hr).ne'
  have hz := (tendsto_log_mul_div ha hb hevent).div_const (4*Real.pi)
  have hv : 4/‖s-t‖^2/(4*Real.pi) = boundaryInteraction s t := by
    simp only [boundaryInteraction]
    field_simp
  rw [hv] at hz
  apply hz.congr'
  exact Filter.Eventually.of_forall fun r => by
    dsimp only
    rw [radial_two_formula s t hs ht]
    have he : (1-r^2)^2/(r^2*‖s-t‖^2) =
        (1-r)^2*((1+r)^2/(r^2*‖s-t‖^2)) := by ring
    rw [he]
    ring

end StrictHotSpots.DiskFormula




open MeasureTheory Filter
open scoped Topology ENNReal


namespace StrictHotSpots.DiskFormula
open MeasureTheory

lemma log_mul_div_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ Real.log (1+a*b)/a ∧ Real.log (1+a*b)/a ≤ b := by
  have h1 : 1 ≤ 1+a*b := by linarith [mul_nonneg ha.le hb]
  constructor
  · exact div_nonneg (Real.log_nonneg h1) ha.le
  · apply (div_le_iff₀ ha).mpr
    have hh := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)
    nlinarith

lemma radial_one_bounded (s x : ℂ) (hs : ‖s‖ = 1)
    {R rmin r : ℝ} (hR : ‖x‖ ≤ R) (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr : r < 1) :
    0 ≤ green (r • s) x / (1-r) ∧
      green (r • s) x / (1-r) ≤ (2/(rmin-R)^2)/(4*Real.pi) := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hR
  have hr0 : 0 ≤ r := hR0.trans (hRmin.le.trans hrmin)
  have hx1 : ‖x‖ < 1 := hR.trans_lt (hRmin.trans_le hrmin |>.trans hr)
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hδ : 0 < rmin-R := sub_pos.mpr hRmin
  have hdist : rmin-R ≤ ‖r • s-x‖ := by
    have hh := norm_sub_norm_le (r • s) x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, hs, mul_one] at hh
    linarith
  have hdist0 : 0 < ‖r • s-x‖ := hδ.trans_le hdist
  have hd2 : (rmin-R)^2 ≤ ‖r • s-x‖^2 := sq_le_sq₀ hδ.le (norm_nonneg _) |>.mpr hdist
  have hnum : (1+r)*(1-‖x‖^2) ≤ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hb0 : 0 ≤ (1+r)*(1-‖x‖^2)/‖r • s-x‖^2 := by positivity
  have hb : (1+r)*(1-‖x‖^2)/‖r • s-x‖^2 ≤ 2/(rmin-R)^2 := by
    calc
      _ ≤ 2/‖r • s-x‖^2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ) hd2
  have hlog := log_mul_div_bounds (sub_pos.mpr hr) hb0
  have he : green (r • s) x/(1-r) =
      (Real.log (1 + (1-r)*((1+r)*(1-‖x‖^2)/‖r • s-x‖^2))/(1-r))/(4*Real.pi) := by
    rw [radial_one_formula s x hs]
    have hh : (1-r^2)*(1-‖x‖^2)/‖r • s-x‖^2 =
        (1-r)*((1+r)*(1-‖x‖^2)/‖r • s-x‖^2) := by ring
    rw [hh]
    ring
  rw [he]
  exact ⟨div_nonneg hlog.1 (by positivity),
    div_le_div_of_nonneg_right (hlog.2.trans hb) (by positivity)⟩

end StrictHotSpots.DiskFormula

namespace StrictHotSpots.DiskFormula
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma poisson_nonneg (s x : ℂ) (hx : ‖x‖ < 1) : 0 ≤ poisson s x := by
  have hh : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  exact div_nonneg hh (by positivity)

lemma poisson_bounded (s x : ℂ) (hs : ‖s‖ = 1)
    {R : ℝ} (hR : ‖x‖ ≤ R) (hR1 : R < 1) :
    poisson s x ≤ 1 / (2*Real.pi*(1-R)^2) := by
  have hh := norm_sub_norm_le s x
  rw [hs] at hh
  have hd : 1-R ≤ ‖s-x‖ := by linarith
  have hd0 : 0 < 1-R := sub_pos.mpr hR1
  have hd2 : (1-R)^2 ≤ ‖s-x‖^2 := (sq_le_sq₀ hd0.le (norm_nonneg _)).mpr hd
  have hn : 1-‖x‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖x‖]
  unfold poisson
  calc
    _ ≤ 1/(2*Real.pi*‖s-x‖^2) := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hd2 (by positivity))

lemma poisson_memLp (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R : ℝ} (hR : ∀ z, ‖x z‖ ≤ R) (hR1 : R < 1) :
    MemLp (fun z => poisson s (x z)) 2 ν := by
  refine MemLp.of_bound ?_ (1 / (2*Real.pi*(1-R)^2)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold poisson
    fun_prop
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (poisson_nonneg s (x z) ((hR z).trans_lt hR1))]
      exact poisson_bounded s (x z) hs (hR z) hR1

lemma radial_one_memLp (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R rmin r : ℝ} (hR : ∀ z, ‖x z‖ ≤ R) (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr : r < 1) :
    MemLp (fun z => green (r • s) (x z)/(1-r)) 2 ν := by
  refine MemLp.of_bound ?_ ((2/(rmin-R)^2)/(4*Real.pi)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold green
    fun_prop
  · exact Filter.Eventually.of_forall fun z => by
      obtain ⟨h0,hb⟩ := radial_one_bounded s (x z) hs (hR z) hRmin hrmin hr
      simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hb



theorem radial_one_L2 (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R rmin : ℝ} (hR : ∀ z, ‖x z‖ ≤ R) (hRmin : R < rmin) (hrmin1 : rmin < 1)
    (r : ℕ → ℝ) (hrmin : ∀ n, rmin ≤ r n) (hr : ∀ n, r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (radial_one_memLp ν s hs x hm hR hRmin (hrmin n) (hr n)).toLp
      (fun z => green (r n • s) (x z) / (1-r n))) atTop
      (𝓝 ((poisson_memLp ν s hs x hm hR (hRmin.trans hrmin1)).toLp
        (fun z => poisson s (x z)))) := by
  apply L2Limits.tendsto_toLp_of_dominated
    (hb := memLp_const ((2/(rmin-R)^2)/(4*Real.pi)))
  · apply Filter.Eventually.of_forall
    intro n
    exact Filter.Eventually.of_forall fun z => by
      obtain ⟨h0,hb⟩ := radial_one_bounded s (x z) hs (hR z) hRmin (hrmin n) (hr n)
      simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hb
  · exact Filter.Eventually.of_forall fun z =>
      (radial_one s (x z) hs ((hR z).trans_lt (hRmin.trans hrmin1))).comp
        (tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall fun n => hr n⟩)

end StrictHotSpots.DiskFormula





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.GreenLp

def logPole (z : ℂ) : ℝ := Real.log (1 + 1 / ‖z‖^2)

lemma logPole_nonneg (z : ℂ) : 0 ≤ logPole z := by
  apply Real.log_nonneg
  have : 0 ≤ 1 / ‖z‖^2 := one_div_nonneg.mpr (sq_nonneg _)
  linarith

lemma measurable_logPole : Measurable logPole := by
  unfold logPole
  fun_prop

lemma logPole_cube_bound {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    (Real.log (1 + 1/t^2))^3 ≤ 648 / t := by
  have harg : 1 + 1/t^2 ≤ (3/t)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    field_simp
    nlinarith
  have hl : Real.log (1 + 1/t^2) ≤ 2 * Real.log (3/t) := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + 1/t^2) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hp : 0 < 3/t := by positivity
  have hr := Real.log_le_rpow_div hp.le (show 0 < (3:ℝ)⁻¹ by norm_num)
  have he : Real.log (1 + 1/t^2) ≤ 6 * (3/t)^((3:ℝ)⁻¹) := by
    norm_num at hr
    linarith
  have hnon : 0 ≤ Real.log (1 + 1/t^2) := by
    apply Real.log_nonneg
    have := one_div_nonneg.mpr (sq_nonneg t)
    linarith
  have hh := pow_le_pow_left₀ hnon he 3
  have hh3 : ((3/t)^((3:ℝ)⁻¹))^3 = 3/t := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hp.le (show (3:ℕ) ≠ 0 by decide)
  rw [mul_pow, hh3] at hh
  calc
    _ ≤ 6^3 * (3/t) := hh
    _ = 648/t := by ring

lemma logPole_cube_integrable : IntegrableOn (fun z : ℂ => (logPole z)^3) (ball 0 2) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 648) (α := 1)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (1:ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    rw [Real.norm_of_nonneg (pow_nonneg (logPole_nonneg z) _), Real.rpow_neg_one]
    by_cases hzero : z = 0
    · simp [hzero, logPole]
    · have hp := norm_pos_iff.mpr hzero
      have hlt : ‖z‖ < 2 := by simpa using hz
      simpa only [logPole, div_eq_mul_inv] using logPole_cube_bound hp hlt.le
  · exact (measurable_logPole.pow_const 3).aestronglyMeasurable

lemma logPole_memLp_three : MemLp logPole 3 (volume.restrict (ball 0 2)) := by
  apply (integrable_norm_rpow_iff measurable_logPole.aestronglyMeasurable
    (by norm_num : (3:ℝ≥0∞) ≠ 0) (by simp : (3:ℝ≥0∞) ≠ (∞ : ℝ≥0∞))).1
  simpa only [IntegrableOn, ENNReal.toReal_ofNat, ← Real.rpow_natCast, Nat.cast_ofNat,
    Real.norm_of_nonneg (logPole_nonneg _)] using logPole_cube_integrable

lemma shifted_logPole_memLp_three (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) := by
  have hpres := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0:ℂ) 2) from measurableSet_ball)
  have hh := logPole_memLp_three.comp_measurePreserving hpres
  have hsub : ball (0:ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0:ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  have hm := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hh
  convert hm using 1
  funext y
  dsimp only [Function.comp_def, logPole]
  rw [norm_sub_rev]

end StrictHotSpots.GreenLp


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma measurable_green_left (x : ℂ) : Measurable (green x) := by
  unfold green
  fun_prop

lemma green_bounds {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    0 ≤ green x y ∧ green x y ≤ logPole (x-y) / (4*Real.pi) := by
  have hwx : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hwy : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : (1-‖x‖^2)*(1-‖y‖^2) ≤ 1 := by
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖, mul_nonneg hwx (sq_nonneg ‖y‖)]
  have hdiv : 0 ≤ (1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 := by positivity
  have hdiv' := div_le_div_of_nonneg_right hn (sq_nonneg ‖x-y‖)
  have hlog : 0 ≤ Real.log (1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2) :=
    Real.log_nonneg (by linarith)
  refine ⟨div_nonneg hlog (by positivity), ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 4*Real.pi)
  exact Real.log_le_log (by linarith) (by simpa only [logPole] using add_le_add_right hdiv' 1)

lemma green_pos {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hne : x ≠ y) :
    0 < green x y := by
  apply div_pos _ (by positivity)
  apply Real.log_pos
  have hwx : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hwy : 0 < 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hd : 0 < ‖x-y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have := div_pos (mul_pos hwx hwy) hd
  linarith

lemma green_memLp_three (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 3 (volume.restrict (ball 0 1)) := by
  have hm : MemLp (fun y => logPole (x-y)/(4*Real.pi)) 3
      (volume.restrict (ball 0 1)) := by
    simpa only [div_eq_mul_inv] using
      (shifted_logPole_memLp_three x hx).mul_const (4*Real.pi)⁻¹
  apply hm.mono (measurable_green_left x).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with y hy
  have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
  have hb := green_bounds hx.le hy'
  rw [Real.norm_of_nonneg hb.1, Real.norm_of_nonneg (div_nonneg (logPole_nonneg (x-y)) (by positivity :
    0 ≤ 4*Real.pi))]
  exact hb.2

lemma green_memLp_two (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 2 (volume.restrict (ball 0 1)) := by
  have : IsFiniteMeasure (volume.restrict (ball (0:ℂ) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using measure_ball_lt_top (x := (0:ℂ)) (r := 1)⟩
  exact (green_memLp_three x hx).mono_exponent (by norm_num)

lemma green_memLp_three_of_le (ν : Measure ℂ) {A : ℝ≥0∞} (hA : A ≠ (∞ : ℝ≥0∞))
    (hν : ν ≤ A • volume.restrict (ball 0 1)) (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 3 ν :=
  MemLp.mono_measure hν ((green_memLp_three x hx).smul_measure hA)

lemma green_memLp_two_of_le (ν : Measure ℂ) {A : ℝ≥0∞} (hA : A ≠ (∞ : ℝ≥0∞))
    (hν : ν ≤ A • volume.restrict (ball 0 1)) (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 2 ν :=
  MemLp.mono_measure hν ((green_memLp_two x hx).smul_measure hA)

end StrictHotSpots.DiskFormula


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.GreenLp

lemma logPole_memLp_two : MemLp logPole 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 2)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  exact logPole_memLp_three.mono_exponent (by norm_num)

lemma shifted_logPole_norm_bound (x : ℂ) (hx : ‖x‖ < 1) :
    eLpNorm (fun y => logPole (x-y)) 2 (volume.restrict (ball 0 1)) ≤
      eLpNorm logPole 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have hs : ball (0 : ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  calc
    _ = eLpNorm (logPole ∘ fun y => y-x) 2 (volume.restrict (ball 0 1)) := by
      congr 1
      funext y
      simp only [Function.comp_apply, logPole, norm_sub_rev x y]
    _ ≤ eLpNorm (logPole ∘ fun y => y-x) 2
        (volume.restrict ((fun y => y-x) ⁻¹' ball 0 2)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)
    _ = _ := eLpNorm_comp_measurePreserving logPole_memLp_two.aestronglyMeasurable hm

end StrictHotSpots.GreenLp
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma green_uniform_L2_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℂ, ‖x‖ < 1 →
    (eLpNorm (green x) 2 (volume.restrict (ball 0 1))).toReal ≤ B := by
  let C := ENNReal.ofReal (4*Real.pi)⁻¹ *
    eLpNorm logPole 2 (volume.restrict (ball (0 : ℂ) 2))
  have hC : C ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top logPole_memLp_two.eLpNorm_ne_top
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun x hx => ?_⟩
  apply ENNReal.toReal_mono hC
  calc
    _ ≤ ENNReal.ofReal (4*Real.pi)⁻¹ *
        eLpNorm (fun y => logPole (x-y)) 2 (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (measurable_green_left x).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
      have hh := green_bounds hx.le hy'
      rw [Real.norm_of_nonneg hh.1, Real.norm_of_nonneg (logPole_nonneg _)]
      simpa only [div_eq_mul_inv, mul_comm] using hh.2
    _ ≤ C := by
      dsimp [C]
      gcongr
      exact shifted_logPole_norm_bound x hx

end StrictHotSpots.DiskFormula



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.MeasurableL2Kernel

lemma integral_mul_eq_inner {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx,hy, RCLike.inner_apply, conj_trivial]
  ring

lemma norm_integral_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖∫ x, f x * g x ∂ν‖ ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  rw [integral_mul_eq_inner hf hg]
  simpa only [Lp.norm_toLp] using norm_inner_le_norm (hf.toLp f) (hg.toLp g)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (K : X × Y → ℝ) (hK : AEStronglyMeasurable K (μ.prod ν))
  (hrow : ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 ν)
  {B : ℝ} (hB : 0 ≤ B)
  (hbound : ∀ᵐ x ∂μ, (eLpNorm (fun y => K (x,y)) 2 ν).toReal ≤ B)

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
include hrow hbound in
lemma apply_bound (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂μ, ‖∫ y, K (x,y) * f y ∂ν‖ ≤ B * ‖f‖ := by
  filter_upwards [hrow, hbound] with x hx hb
  have hh := norm_integral_mul_le hx (Lp.memLp f)
  have he : (eLpNorm (fun y => f y) 2 ν).toReal = ‖f‖ := rfl
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f))

include hK hrow hbound in
lemma apply_memLp (f : Lp ℝ 2 ν) :
    MemLp (fun x => ∫ y, K (x,y) * f y ∂ν) 2 μ := by
  have hm : AEStronglyMeasurable (fun z : X × Y => K z * f z.2) (μ.prod ν) :=
    hK.mul (Lp.aestronglyMeasurable f).comp_snd
  exact MemLp.of_bound hm.integral_prod_right' (B * ‖f‖)
    (apply_bound K hrow hbound f)



def operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ := by
  let T : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun f => (apply_memLp K hK hrow hbound f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(apply_memLp K hK hrow hbound (f+g)).coeFn_toLp,
          (apply_memLp K hK hrow hbound f).coeFn_toLp,
          (apply_memLp K hK hrow hbound g).coeFn_toLp,
          Lp.coeFn_add ((apply_memLp K hK hrow hbound f).toLp _)
            ((apply_memLp K hK hrow hbound g).toLp _), hrow] with x hx hf hg ha hr
        rw [hx,ha, Pi.add_apply,hf,hg]
        have he : (fun y => K (x,y) * (f+g) y) =ᵐ[ν]
            (fun y => K (x,y) * f y + K (x,y) * g y) := by
          filter_upwards [Lp.coeFn_add f g] with y hy
          rw [hy, Pi.add_apply, mul_add]
        rw [integral_congr_ae he, integral_add]
        · exact hr.integrable_mul (Lp.memLp f)
        · exact hr.integrable_mul (Lp.memLp g)
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(apply_memLp K hK hrow hbound (c • f)).coeFn_toLp,
          (apply_memLp K hK hrow hbound f).coeFn_toLp,
          Lp.coeFn_smul c ((apply_memLp K hK hrow hbound f).toLp _)] with x hx hf hs
        simp only [RingHom.id_apply]
        rw [hx,hs, Pi.smul_apply,hf]
        have he : (fun y => K (x,y) * (c • f) y) =ᵐ[ν]
            (fun y => c * (K (x,y) * f y)) := by
          filter_upwards [Lp.coeFn_smul c f] with y hy
          rw [hy, Pi.smul_apply, smul_eq_mul]
          ring
        rw [integral_congr_ae he, integral_const_mul, smul_eq_mul] }
  refine T.mkContinuous ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * B) ?_
  intro f
  have hh := Lp.norm_le_of_ae_bound (mul_nonneg hB (norm_nonneg f))
    (show ∀ᵐ x ∂μ, ‖T f x‖ ≤ B * ‖f‖ from by
      filter_upwards [(apply_memLp K hK hrow hbound f).coeFn_toLp,
        apply_bound K hrow hbound f] with x hx hb
      change ‖((apply_memLp K hK hrow hbound f).toLp _) x‖ ≤ _
      rw [hx]
      exact hb)
  exact hh.trans_eq (mul_assoc _ _ _).symm

lemma operator_apply_ae (f : Lp ℝ 2 ν) :
    operator K hK hrow hB hbound f =ᵐ[μ] fun x => ∫ y, K (x,y) * f y ∂ν :=
  (apply_memLp K hK hrow hbound f).coeFn_toLp

end StrictHotSpots.MeasurableL2Kernel



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology
namespace StrictHotSpots

lemma eq_zero_of_inner_smoothTest_eq_zero {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ φ : smoothTestSpace Ω, inner ℝ (H1.value (smoothTestToH1 hΩ φ)) u = 0) :
    u = 0 := by
  have hl := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
    (fun φ hp hc hs => show (∫ x in Ω, φ x • u x) = 0 from by
      have ht := h ⟨φ,hp,hc,hs⟩
      have hv : H1.value (smoothTestToH1 hΩ ⟨φ,hp,hc,hs⟩) =
          (test_memLp (Ω := Ω) hp hc).toLp φ := rfl
      rw [hv, L2.inner_def] at ht
      convert ht using 1
      apply integral_congr_ae
      filter_upwards [(test_memLp (Ω := Ω) hp hc).coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      ring)
  apply Lp.ext
  filter_upwards [hh, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x hx hΩx hz
  rw [hz]
  exact hx hΩx

lemma smoothTest_dense_L2 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (fun φ : smoothTestSpace Ω => H1.value (smoothTestToH1 hΩ φ)) := by
  let T : smoothTestSpace Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    H1.value.toLinearMap.comp (smoothTestToH1 hΩ)
  have hz : T.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    change u = 0
    apply eq_zero_of_inner_smoothTest_eq_zero hΩ u
    intro φ
    exact (Submodule.mem_orthogonal _ _).mp hu (T φ) ⟨φ,rfl⟩
  have ht : T.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hz, Submodule.bot_orthogonal_eq_top]
  have hd : closure (Set.range T) = Set.univ := by
    change closure (T.range : Set (Lp ℝ 2 (volume.restrict Ω))) = Set.univ
    rw [← Submodule.topologicalClosure_coe, ht, Submodule.top_coe]
  exact dense_iff_closure_eq.mpr hd

end StrictHotSpots







open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def solution (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) :
    H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp J.adjoint

lemma solution_spec (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) (v : V) : B (solution B hB J f) v = ⟪f, J v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp only [solution, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]


def green (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) :
    H →L[ℝ] H := J.comp (solution B hB J)

lemma green_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) : green B hB J f = J (solution B hB J f) := rfl

lemma green_symmetric (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (f g : H) :
    ⟪green B hB J f, g⟫_ℝ = ⟪f, green B hB J g⟫_ℝ := by
  calc
    _ = ⟪g, J (solution B hB J f)⟫_ℝ := real_inner_comm _ _
    _ = B (solution B hB J g) (solution B hB J f) := (solution_spec B hB J g _).symm
    _ = B (solution B hB J f) (solution B hB J g) := hsym _ _
    _ = _ := solution_spec B hB J f _

lemma green_nonneg (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (f : H) : 0 ≤ ⟪f, green B hB J f⟫_ℝ := by
  rw [green_apply, ← solution_spec B hB J f (solution B hB J f)]
  obtain ⟨C, hC, h⟩ := hB
  exact (mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (norm_nonneg _)).trans (h _)



lemma green_norm_le (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ v : V, ‖J v‖ ^ 2 ≤ d * B v v) : ‖green B hB J‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  let u := solution B hB J f
  have h0 := hsub u
  have hs : B u u = ⟪f, J u⟫_ℝ := solution_spec B hB J f u
  rw [hs] at h0
  have hi : ⟪f, J u⟫_ℝ ≤ ‖f‖ * ‖J u‖ := real_inner_le_norm _ _
  have ht : ‖J u‖ ^ 2 ≤ d * (‖f‖ * ‖J u‖) :=
    h0.trans (mul_le_mul_of_nonneg_left hi hd)
  change ‖J u‖ ≤ d * ‖f‖
  by_cases hz : ‖J u‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖J u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma green_norm_lt_one (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : V, ‖J v‖ ^ 2 ≤ d * B v v) : ‖green B hB J‖ < 1 :=
  (green_norm_le B hB J hd hsub).trans_lt hd1

end StrictHotSpots.DirichletOperator


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma diskBounded : Bornology.IsBounded disk := Metric.isBounded_ball

instance diskFinite : IsFiniteMeasure (volume.restrict disk) :=
  isFiniteMeasure_restrict.mpr diskBounded.measure_lt_top.ne

def kernel (x y : Plane) : ℝ := DiskFormula.green (complexIso.symm x) (complexIso.symm y)

lemma complexIso_disk_preserving : MeasurePreserving complexIso.symm
    (volume.restrict disk) (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  have h := complexIso.symm.measurePreserving.restrict_preimage
    (show MeasurableSet (Metric.ball (0 : ℂ) 1) from measurableSet_ball)
  have he : complexIso.symm ⁻¹' Metric.ball (0 : ℂ) 1 = disk := by
    ext x
    simp [disk]
  rwa [he] at h

lemma kernel_memLp (x : Plane) (hx : x ∈ disk) :
    MemLp (kernel x) 2 (volume.restrict disk) := by
  have hx' : ‖complexIso.symm x‖ < 1 := by simpa [disk] using hx
  exact (DiskFormula.green_memLp_two _ hx').comp_measurePreserving complexIso_disk_preserving

lemma measurable_kernel : Measurable (fun p : Plane × Plane => kernel p.1 p.2) := by
  unfold kernel DiskFormula.green
  fun_prop

lemma kernel_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ disk,
    (eLpNorm (kernel x) 2 (volume.restrict disk)).toReal ≤ B := by
  obtain ⟨B,hB,h⟩ := DiskFormula.green_uniform_L2_bound
  refine ⟨B,hB,fun x hx => ?_⟩
  have hx' : ‖complexIso.symm x‖ < 1 := by simpa [disk] using hx
  have he := eLpNorm_comp_measurePreserving (p := 2)
    (DiskFormula.green_memLp_two _ hx').aestronglyMeasurable complexIso_disk_preserving
  change (eLpNorm (DiskFormula.green (complexIso.symm x) ∘ complexIso.symm) 2
    (volume.restrict disk)).toReal ≤ B
  rw [he]
  exact h _ hx'

lemma kernel_rows : ∀ᵐ x ∂volume.restrict disk, MemLp (kernel x) 2 (volume.restrict disk) := by
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  exact kernel_memLp x hx

def integralOperator : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
  MeasurableL2Kernel.operator (fun p => kernel p.1 p.2) measurable_kernel.aestronglyMeasurable
    kernel_rows kernel_bound.choose_spec.1
    (by filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
        exact kernel_bound.choose_spec.2 x hx)

lemma integralOperator_ae (f : Lp ℝ 2 (volume.restrict disk)) :
    integralOperator f =ᵐ[volume.restrict disk] fun x => ∫ y in disk, kernel x y * f y :=
  MeasurableL2Kernel.operator_apply_ae _ _ _ _ _ f

lemma potential_eq_integral {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) {x : Plane} (hx : x ∈ disk) :
    potential f x = ∫ y in disk, kernel x y * f y := by
  obtain ⟨R,hR,hn⟩ := GreenPotential.exists_regular_neighborhood (source_compact hc)
    (source_support hs)
  have hx' : complexIso.symm x ∈ Metric.ball (0 : ℂ) R := by
    have : ‖x‖ < 1 := by simpa [disk] using hx
    simpa using this.trans hR
  have hh := GreenPotential.potential_eq_integral (source_contDiff hf) (source_compact hc)
    Metric.isOpen_ball hn hx'
  change GreenPotential.potential (source f) (complexIso.symm x) = _
  rw [hh]
  have he := complexIso.symm.measurePreserving.integral_comp
    complexIso.symm.toMeasurableEquiv.measurableEmbedding
    (fun z => DiskFormula.green (complexIso.symm x) z * source f z)
  simp only [source, complexIso.apply_symm_apply] at he
  simp only [source]
  rw [← he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
  simp [hfy, kernel]

def variationalOperator : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
  @DirichletOperator.green (H10 diskOpen) (Lp ℝ 2 (volume.restrict disk))
    (H10.normedAddCommGroup diskOpen) (H10.innerProductSpace diskOpen)
    (H10.completeSpace diskOpen) inferInstance inferInstance inferInstance
    (H10.energy diskOpen) (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen)

lemma variationalOperator_test (f : smoothTestSpace disk) :
    variationalOperator (H1.value (smoothTestToH1 diskOpen f)) =ᵐ[volume.restrict disk]
      potential f := by
  obtain ⟨u,hu,he⟩ := exists_dirichlet_representative f.property.1 f.property.2.1 f.property.2.2
  let w := DirichletOperator.solution (H10.energy diskOpen)
    (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen)
    (H1.value (smoothTestToH1 diskOpen f))
  have hw : ∀ v, H10.energy diskOpen w v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) :=
    DirichletOperator.solution_spec _ _ _ _
  have he' : ∀ v, H10.energy diskOpen u v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) := he
  obtain ⟨_,_,hun⟩ := H10.existsUnique_energy_solution diskOpen diskBounded
    ((innerSL ℝ (H1.value (smoothTestToH1 diskOpen f))).comp (H10.value diskOpen))
  have heq : w = u := (hun w hw).trans (hun u he').symm
  change H10.value diskOpen w =ᵐ[volume.restrict disk] potential f
  rw [heq]
  exact hu



lemma integralOperator_eq_variationalOperator : integralOperator = variationalOperator := by
  apply DFunLike.coe_injective
  apply (smoothTest_dense_L2 diskOpen).equalizer integralOperator.continuous
    variationalOperator.continuous
  funext f
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [integralOperator_ae (H1.value (smoothTestToH1 diskOpen f)),
    variationalOperator_test f, ae_restrict_mem diskOpen.measurableSet] with x hx hu hxd
  rw [hx,hu,potential_eq_integral f.property.1 f.property.2.1 f.property.2.2 hxd]
  apply integral_congr_ae
  have hf : H1.value (smoothTestToH1 diskOpen f) =ᵐ[volume.restrict disk] f :=
    (test_memLp (Ω := disk) f.property.1 f.property.2.1).coeFn_toLp
  filter_upwards [hf] with y hy
  rw [hy]

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict Ω)


def weightedValue : H10 hΩ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.LpToLpOfMeasureLeSMul hC hν).comp (value hΩ)

lemma weightedValue_ae (u : H10 hΩ) :
    weightedValue hΩ hC hν u =ᵐ[ν] value hΩ u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (value hΩ u)



def greenOperator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  @DirichletOperator.green (H10 hΩ) (Lp ℝ 2 ν)
    (H10.normedAddCommGroup hΩ) (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    inferInstance inferInstance inferInstance
    (energy hΩ) (energy_coercive hΩ hb) (weightedValue hΩ hC hν)

lemma energy_symmetric (u v : H10 hΩ) : energy hΩ u v = energy hΩ v u := by
  calc
    energy hΩ u v = inner ℝ (grad hΩ u) (grad hΩ v) := energy_apply hΩ u v
    _ = inner ℝ (grad hΩ v) (grad hΩ u) := real_inner_comm _ _
    _ = energy hΩ v u := (energy_apply hΩ v u).symm

lemma greenOperator_symmetric (f g : Lp ℝ 2 ν) :
    inner ℝ (greenOperator hΩ hb hC hν f) g =
      inner ℝ f (greenOperator hΩ hb hC hν g) :=
  DirichletOperator.green_symmetric (energy hΩ) (energy_coercive hΩ hb)
    (energy_symmetric hΩ) (weightedValue hΩ hC hν) f g

lemma greenOperator_nonneg (f : Lp ℝ 2 ν) :
    0 ≤ inner ℝ f (greenOperator hΩ hb hC hν f) :=
  DirichletOperator.green_nonneg (energy hΩ) (energy_coercive hΩ hb)
    (weightedValue hΩ hC hν) f


lemma greenOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 hΩ, ‖weightedValue hΩ hC hν u‖ ^ 2 ≤
      d * ‖grad hΩ u‖ ^ 2) : ‖greenOperator hΩ hb hC hν‖ ≤ d := by
  apply DirichletOperator.green_norm_le (energy hΩ) (energy_coercive hΩ hb)
    (weightedValue hΩ hC hν) hd
  intro u
  simpa only [energy_apply, real_inner_self_eq_norm_sq] using hsub u

end StrictHotSpots.H10


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.DirichletOperator

lemma green_comp {V H K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) (S : H →L[ℝ] K) :
    green B hB (S.comp J) = (S.comp (green B hB J)).comp S.adjoint := by
  simp only [green, solution, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end StrictHotSpots.DirichletOperator
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

def inclusion : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 ν :=
  Lp.LpToLpOfMeasureLeSMul hC hν

lemma inclusion_ae (f : Lp ℝ 2 (volume.restrict disk)) : inclusion hC hν f =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν f

include hC hν in
lemma kernel_memLp_weighted (x : Plane) (hx : x ∈ disk) : MemLp (kernel x) 2 ν :=
  ((kernel_memLp x hx).smul_measure hC).mono_measure hν

lemma inclusion_row (x : Plane) (hx : x ∈ disk) :
    inclusion hC hν ((kernel_memLp x hx).toLp (kernel x)) =
      (kernel_memLp_weighted hC hν x hx).toLp (kernel x) := by
  apply Lp.ext
  exact (inclusion_ae hC hν _).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq (kernel_memLp x hx).coeFn_toLp).trans
      (kernel_memLp_weighted hC hν x hx).coeFn_toLp.symm)

lemma integral_adjoint_row (f : Lp ℝ 2 ν) (x : Plane) (hx : x ∈ disk) :
    (∫ y in disk, kernel x y * (inclusion hC hν).adjoint f y) =
      ∫ y, kernel x y * f y ∂ν := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp x hx)
    (Lp.memLp ((inclusion hC hν).adjoint f)), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, inclusion_row hC hν x hx]
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp_weighted hC hν x hx)
    (Lp.memLp f), Lp.toLp_coeFn]



def weightedIntegralOperator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ((inclusion hC hν).comp integralOperator).comp (inclusion hC hν).adjoint

lemma weightedIntegralOperator_ae (f : Lp ℝ 2 ν) :
    weightedIntegralOperator hC hν f =ᵐ[ν] fun x => ∫ y, kernel x y * f y ∂ν := by
  have ha := (Measure.absolutelyContinuous_of_le_smul hν)
  filter_upwards [inclusion_ae hC hν (integralOperator ((inclusion hC hν).adjoint f)),
    ha.ae_eq (integralOperator_ae ((inclusion hC hν).adjoint f)),
    (ae_restrict_mem diskOpen.measurableSet).filter_mono ha.ae_le] with x hx hi hxd
  change inclusion hC hν (integralOperator ((inclusion hC hν).adjoint f)) x = _
  rw [hx,hi,integral_adjoint_row hC hν f x hxd]

lemma weightedIntegralOperator_eq_greenOperator : weightedIntegralOperator hC hν =
    H10.greenOperator diskOpen diskBounded hC hν := by
  unfold weightedIntegralOperator H10.greenOperator H10.weightedValue

  rw [DirichletOperator.green_comp, integralOperator_eq_variationalOperator]
  rfl



lemma weightedIntegralOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) : ‖weightedIntegralOperator hC hν‖ ≤ d := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_norm_le diskOpen diskBounded hC hν hd hsub

lemma weightedIntegralOperator_symmetric (f g : Lp ℝ 2 ν) :
    inner ℝ (weightedIntegralOperator hC hν f) g =
      inner ℝ f (weightedIntegralOperator hC hν g) := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_symmetric diskOpen diskBounded hC hν f g

lemma weightedIntegralOperator_nonneg (f : Lp ℝ 2 ν) :
    0 ≤ inner ℝ f (weightedIntegralOperator hC hν f) := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_nonneg diskOpen diskBounded hC hν f

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
