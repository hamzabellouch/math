import Mathlib
import OAI.Probability.SLELocalization.ConditionalAngles
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Loewner Exit estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerExit
open LoewnerCutoff

lemma stop_le_of_nonpos {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (U : C(I,ℝ)) (z : ℂ) (ρ δ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hn : deficit hε hT.le U z ρ δ t ≤ 0) :
    stop hε hT.le U z ρ δ ≤ t := by
  have hq : t/T ∈ Icc (0:ℝ) 1 := ⟨div_nonneg ht.1 hT.le,(div_le_one hT).2 ht.2⟩
  have hh := ContinuousExit.time_le_of_nonpos hq
    (show ContinuousExit.extend (exitPath hε hT.le U z ρ δ) (t/T) ≤ 0 by
      rw [exitPath_extend_div hε hT.le hT U z ρ δ ht]; exact hn)
  change T*ContinuousExit.time (exitPath hε hT.le U z ρ δ) ≤ t
  exact (mul_le_mul_of_nonneg_left hh hT.le).trans_eq (mul_div_cancel₀ _ hT.ne')

lemma stop_prefix_min {ε S T : ℝ} (hε : 0 < ε) (hS : 0 < S) (hT : 0 < T)
    (hST : S ≤ T) (U V : C(I,ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S)) :
    stop hε hS.le U z ρ δ = min S (stop hε hT.le V z ρ δ) := by
  let a := stop hε hS.le U z ρ δ
  let b := stop hε hT.le V z ρ δ
  have ha : 0 ≤ a ∧ a ≤ S := stop_bounds hε hS.le U z ρ δ
  have hb : 0 ≤ b ∧ b ≤ T := stop_bounds hε hT.le V z ρ δ
  have hd := deficit_prefix_eq hε hS.le hT.le hST U V z ρ δ hUV
  apply le_antisymm
  · apply le_min ha.2
    by_contra hn
    have hba : b < a := lt_of_not_ge hn
    have hbs : b < S := hba.trans_le ha.2
    have hbT : b < T := hbs.trans_le hST
    have hn := nonpos_at_of_lt hε hT.le hT V z ρ δ hbT
    have hp := positive_before hε hS.le hS U z ρ δ hb.1 hba
    have he := hd ⟨hb.1,hbs.le⟩
    change deficit hε hS.le U z ρ δ b = deficit hε hT.le V z ρ δ b at he
    rw [he] at hp
    exact (not_lt_of_ge hn) hp
  · by_contra hn
    have haa : a < min S b := lt_of_not_ge hn
    have haS : a < S := (lt_min_iff.1 haa).1
    have hab : a < b := (lt_min_iff.1 haa).2
    have hn := nonpos_at_of_lt hε hS.le hS U z ρ δ haS
    have hp := positive_before hε hT.le hT V z ρ δ ha.1 hab
    have he := hd ⟨ha.1,haS.le⟩
    change deficit hε hS.le U z ρ δ a = deficit hε hT.le V z ρ δ a at he
    rw [← he] at hp
    exact (not_lt_of_ge hn) hp

end SLEExactGauge.LoewnerExit

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff

def withHorizon {z : ℂ} {u : ℝ} (C : Cutoff z u) (T : ℝ≥0) : Cutoff z u where
  angle := C.angle
  angle_pos := C.angle_pos
  angle_initial := C.angle_initial
  height := C.height
  height_pos := C.height_pos
  horizon := max C.horizon (T+1)
  horizon_pos := C.horizon_pos.trans_le (le_max_left _ _)
  height_small := C.height_small
  time_large := C.time_large.trans_le (le_max_left _ _)

lemma withHorizon_gt {z : ℂ} {u : ℝ} (C : Cutoff z u) (T : ℝ≥0) :
    (T:ℝ) < (C.withHorizon T).horizon := by
  change (T:ℝ) < max (C.horizon:ℝ) (T+1)
  exact (lt_add_one _).trans_le (le_max_right _ _)

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.RadiusPast
open LoewnerCutoff LoewnerExit LoewnerLocalized FiniteTilt

def hitData {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (κ : ℝ) (U : C(I,ℝ)) (z : ℂ) (ρ δ : ℝ) : ℝ × ℝ :=
  let τ := stop hε hT U z ρ δ
  (τ, if radius hε hT U z τ ≤ ρ then
    (radius hε hT U z τ)^(-codimension κ)*(sine hε hT U z τ)^(8/κ-1) else 0)

lemma measurable_hitData {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (κ : ℝ) (z : ℂ) (ρ δ : ℝ) :
    @Measurable C(I,ℝ) (ℝ × ℝ) (borel _) _ (fun U => hitData hε hT.le κ U z ρ δ) := by
  let : MeasurableSpace C(I,ℝ) := borel _
  let : BorelSpace C(I,ℝ) := ⟨rfl⟩
  have ht := GammaField.measurable_stop hε hT.le hT z ρ δ
  have hr := (continuous_radius hε hT.le z).measurable.comp (measurable_id.prodMk ht)
  have hs := (continuous_sine hε hT.le z).measurable.comp (measurable_id.prodMk ht)
  exact ht.prodMk (Measurable.ite (measurableSet_le hr measurable_const)
    ((hr.pow_const _).mul (hs.pow_const _)) measurable_const)

end SLEExactGauge.RadiusPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.RadiusPast
open LoewnerCutoff LoewnerExit LoewnerLocalized FiniteTilt
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
variable (C : Cutoff z u) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (hTC : T ≤ C.horizon)

include h hz hu hc hb0 hT hTC in
lemma raw_data_source :
    let U := BrownianDriver.path B (Real.sqrt κ) T sample
    let τ := stop C.height_pos T.coe_nonneg U z ((2*z.im)*Real.exp (-u)) C.angle
    τ = min (T:ℝ) (C.stopTime κ B sample) ∧ z ∈ localizationDomain γ τ ∧
    hitData C.height_pos T.coe_nonneg κ U z ((2*z.im)*Real.exp (-u)) C.angle =
      (τ, if loewnerRadius g τ z = (2*z.im)*Real.exp (-u) then
        (loewnerRadius g τ z)^(-codimension κ) *
          (loewnerAngleSine κ (fun t => B t sample) g τ z)^(8/κ-1) else 0) := by
  classical
  dsimp only
  let U := BrownianDriver.path B (Real.sqrt κ) T sample
  let ρ := (2*z.im)*Real.exp (-u)
  let τ := stop C.height_pos T.coe_nonneg U z ρ C.angle
  have hUV := BrownianDriver.prefix_eq B (Real.sqrt κ) T C.horizon sample hc hTC
  have h0 : 0 < deficit C.height_pos T.coe_nonneg U z ρ C.angle 0 := by
    rw [deficit_prefix_eq C.height_pos T.coe_nonneg C.horizon.coe_nonneg hTC
      U (C.paths κ B sample) z ρ C.angle hUV ⟨le_rfl,T.coe_nonneg⟩]
    exact C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hU : EqOn (extendDriver T U) (fun t => Real.sqrt κ*B t.toNNReal sample) (Icc 0 (T:ℝ)) :=
    fun t ht => BrownianDriver.extend_eq B (Real.sqrt κ) T sample hc ht
  have hsrc := source_until_stop C.height_pos hT h U z ρ C.angle hU h0
  have hb := stop_bounds C.height_pos T.coe_nonneg U z ρ C.angle
  have ht : τ ∈ Icc 0 τ := ⟨hb.1,le_rfl⟩
  have hr := radius_eq_source C.height_pos hT h
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) U z ρ C.angle hU h0 ht
  have hs : sine C.height_pos T.coe_nonneg U z τ =
      loewnerAngleSine κ (fun t => B t sample) g τ z := by
    simpa only [loewnerAngleSine,Complex.ofReal_mul] using
      sine_eq_source C.height_pos hT h U z ρ C.angle hU h0 ht
  have hlo : ρ ≤ radius C.height_pos T.coe_nonneg U z τ :=
    ((deficit_nonneg_iff C.height_pos T.coe_nonneg U z ρ C.angle τ).1
      (nonneg_until C.height_pos T.coe_nonneg hT U z ρ C.angle h0 ht)).1
  refine ⟨stop_prefix_min C.height_pos hT C.horizon_pos hTC U (C.paths κ B sample) z ρ C.angle hUV,hsrc.1,?_⟩
  change (τ, if radius C.height_pos T.coe_nonneg U z τ ≤ ρ then
    (radius C.height_pos T.coe_nonneg U z τ)^(-codimension κ) *
    (sine C.height_pos T.coe_nonneg U z τ)^(8/κ-1) else 0) =
    (τ, if loewnerRadius g τ z = ρ then (loewnerRadius g τ z)^(-codimension κ) *
      (loewnerAngleSine κ (fun t => B t sample) g τ z)^(8/κ-1) else 0)
  by_cases he : loewnerRadius g τ z = ρ
  · have hle : radius C.height_pos T.coe_nonneg U z τ ≤ ρ := by rw [hr,he]
    simp only [hr,hs,he,le_refl,ite_true]
  · have hn : ¬ radius C.height_pos T.coe_nonneg U z τ ≤ ρ := by
      intro hl
      exact he (hr.symm.trans (le_antisymm hl hlo))
    simp only [hn,he,ite_false]

include h hz hu hc hb0 in
lemma eventually_stop_general (D : ℕ → Cutoff z u)
    (hD : Tendsto (fun n => (D n).angle) atTop (𝓝 0))
    {t : ℝ≥0} (hzt : z ∈ localizationDomain γ t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    ∀ᶠ n : ℕ in atTop, (D n).stopTime κ B sample = t := by
  obtain ⟨η,hη,hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  filter_upwards [hD.eventually (gt_mem_nhds hη)] with n hn
  let C := D n
  have hh : loewnerRadius g (C.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) := by
    rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · exact hr
    · have htm := hm (C.stopTime κ B sample)
        ⟨(C.bounds κ B sample).1,C.stopTime_le_radius κ B sample h hz hu hc hb0 t.coe_nonneg hzt hrt⟩
      rw [hs] at htm
      exact False.elim ((not_lt_of_ge htm) hn)
  exact h.live_radius_injective
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.bounds κ B sample).1 t.coe_nonneg (C.source_live κ B sample h hz hu hc hb0) hzt
    (hh.trans hrt.symm)

end SLEExactGauge.RadiusPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.RadiusPast
open LoewnerCutoff LoewnerExit LoewnerLocalized FiniteTilt

lemma live_radius_witness {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hU : ContinuousOn driver (Ici 0))
    {z : ℂ} {u : ℝ} (hh : firstLiveRadiusStop γ g z u ≠ (⊤ : ℝ≥0∞)) :
    ∃ t : ℝ≥0, firstLiveRadiusStop γ g z u = (t : ℝ≥0∞) ∧
      z ∈ localizationDomain γ t ∧ loewnerRadius g t z = (2*z.im)*Real.exp (-u) := by
  have he : ∃ t : ℝ≥0, z ∈ localizationDomain γ t ∧
      loewnerRadius g t z = (2*z.im)*Real.exp (-u) := by
    by_contra hn
    have he : {t : ℝ≥0 | z ∈ localizationDomain γ t ∧
        loewnerRadius g t z = (2*z.im)*Real.exp (-u)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (fun t ht => hn ⟨t,ht⟩)
    exact hh (by simp only [firstLiveRadiusStop,he,Set.image_empty,sInf_empty])
  obtain ⟨t,hzt,hrt⟩ := he
  exact ⟨t,h.firstLiveRadiusStop_eq hU hzt hrt,hzt,hrt⟩

def byTime {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) (T : ℝ≥0) (sample : Ω) : ℝ≥0∞ :=
  if firstLiveRadiusStop (γ sample) (g sample) z u ≤ (T : ℝ≥0∞) then
    finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u else 0

def approx {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {z : ℂ} (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) (n : ℕ) (sample : Ω) : ℝ≥0∞ :=
  let C := (cutoffs hz u hu n).withHorizon T
  ENNReal.ofReal (hitData C.height_pos T.coe_nonneg κ
    (BrownianDriver.path B (Real.sqrt κ) T sample) z ((2*z.im)*Real.exp (-u)) C.angle).2

lemma eventually_approx {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
    (T : ℝ≥0) (hT : 0 < (T:ℝ)) :
    ∀ᶠ n : ℕ in atTop, approx κ B hz u hu.le T n sample = byTime κ B γ g z u T sample := by
  classical
  let D := fun n => (cutoffs hz u hu.le n).withHorizon T
  have hU : ContinuousOn (fun t : ℝ => Real.sqrt κ*B t.toNNReal sample) (Ici 0) := (continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn
  by_cases hh : firstLiveRadiusStop (γ sample) (g sample) z u ≤ (T : ℝ≥0∞)
  · obtain ⟨t,htau,hzt,hrt⟩ := live_radius_witness h hU
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hh)
    have htT : t ≤ T := by simpa only [htau,ENNReal.coe_le_coe] using hh
    have hD : Tendsto (fun n => (D n).angle) atTop (𝓝 0) := shrinkingAngle_tendsto z
    filter_upwards [eventually_stop_general κ B sample h hz hu hc hb0 D hD hzt hrt] with n hn
    have hs := raw_data_source κ B sample h hz hu hc hb0 (D n) T hT
      ((cutoffs hz u hu.le n).withHorizon_gt T).le
    dsimp only at hs
    rw [hn,min_eq_right (show (t:ℝ) ≤ T from htT)] at hs
    dsimp only [approx]
    unfold byTime
    rw [ite_eq_left hh, hs.2.2, Prod.snd, hs.1, ite_eq_left hrt,
      finiteStoppedDensity,htau,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal]
  · apply Filter.Eventually.of_forall
    intro n
    have hs := raw_data_source κ B sample h hz hu hc hb0 (D n) T hT
      ((cutoffs hz u hu.le n).withHorizon_gt T).le
    dsimp only at hs
    let U := BrownianDriver.path B (Real.sqrt κ) T sample
    let τ := stop (D n).height_pos T.coe_nonneg U z ((2*z.im)*Real.exp (-u)) (D n).angle
    have hn : loewnerRadius (g sample) τ z ≠ (2*z.im)*Real.exp (-u) := by
      intro he
      have ht := stop_bounds (D n).height_pos T.coe_nonneg U z ((2*z.im)*Real.exp (-u)) (D n).angle
      have heq := h.firstLiveRadiusStop_eq hU (t := ⟨τ,ht.1⟩) hs.2.1 he
      apply hh
      rw [heq]
      exact ENNReal.coe_le_coe.2 (show (⟨τ,ht.1⟩ : ℝ≥0) ≤ T from ht.2)
    dsimp only [approx]
    unfold byTime
    rw [ite_eq_right hh,hs.2.2,Prod.snd,ite_eq_right hn,ENNReal.ofReal_zero]

end SLEExactGauge.RadiusPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.RadiusPast
open FiniteTilt BrownianPredictable
local instance : MeasurableSpace C(I, ℝ) := borel _
local instance : BorelSpace C(I, ℝ) := ⟨rfl⟩

def observed {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {z : ℂ} (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) (sample : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (ContinuousDriver.selectedLimit 0 (fun n => (approx κ B hz u hu T n sample).toReal))

lemma measurable_observed {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {z : ℂ} (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) (hT : 0 < (T:ℝ)) :
    Measurable[pastSigma B T] (observed κ B hz u hu T) := by
  let : MeasurableSpace Ω := pastSigma B T
  apply ENNReal.measurable_ofReal.comp
  apply ContinuousDriver.measurable_selectedLimit
  intro n
  let C := (cutoffs hz u hu n).withHorizon T
  exact ENNReal.measurable_toReal.comp (ENNReal.measurable_ofReal.comp
    (((measurable_hitData C.height_pos hT κ z ((2*z.im)*Real.exp (-u)) C.angle).snd).comp
      (BrownianDriver.path_measurable_past B (Real.sqrt κ) T)))

lemma aemeasurable_observed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {z : ℂ} (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) (hT : 0 < (T:ℝ)) :
    AEMeasurable (observed κ B hz u hu T) P := by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  apply ContinuousDriver.aemeasurable_selectedLimit
  intro n
  let C := (cutoffs hz u hu n).withHorizon T
  exact ENNReal.measurable_toReal.comp_aemeasurable (ENNReal.measurable_ofReal.comp_aemeasurable
    (((measurable_hitData C.height_pos hT κ z ((2*z.im)*Real.exp (-u)) C.angle).snd).comp_aemeasurable
      (BrownianDriver.path_aemeasurable hB (Real.sqrt κ) T)))

lemma observed_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
    (T : ℝ≥0) (hT : 0 < (T:ℝ)) :
    observed κ B hz u hu.le T sample = byTime κ B γ g z u T sample := by
  have hf : byTime κ B γ g z u T sample ≠ ⊤ := by
    simp only [byTime,finiteStoppedDensity]
    split_ifs <;> simp
  unfold observed
  rw [ContinuousDriver.selectedLimit_eq (y := (byTime κ B γ g z u T sample).toReal) 0 (by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_approx κ B γ g f sample h hz hu hc hb0 T hT] with n hn
    exact congrArg ENNReal.toReal hn.symm), ENNReal.ofReal_toReal hf]

lemma byTime_pos_iff {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (_hz : z ∈ halfPlane) (u : ℝ)
    (hc : Continuous (fun t => B t sample)) (T : ℝ≥0) :
    0 < byTime κ B γ g z u T sample ↔ firstLiveRadiusStop (γ sample) (g sample) z u ≤ (T : ℝ≥0∞) := by
  unfold byTime
  split_ifs with hh
  · obtain ⟨t,htau,hzt,hrt⟩ := live_radius_witness h
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hh)
    have hs : 0 < loewnerAngleSine κ (fun t => B t sample) (g sample) t z := by
      simpa only [loewnerAngleSine,Complex.ofReal_mul] using
        div_pos (h.im_pos t.coe_nonneg hzt) (norm_pos_iff.2 (h.centered_ne_zero t.coe_nonneg hzt))
    have hr : 0 < loewnerRadius (g sample) t z := h.radius_pos t.coe_nonneg hzt
    simp only [finiteStoppedDensity,htau,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal]
    exact iff_of_true (ENNReal.ofReal_pos.2
      (mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hs _))) (htau ▸ hh)
  · exact iff_of_false (lt_irrefl _) hh

end SLEExactGauge.RadiusPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing driver γ g f) (hU : ContinuousOn driver (Ici 0))

include h hU in
lemma firstLiveRadiusStop_mono {z : ℂ} (hz : z ∈ halfPlane) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    firstLiveRadiusStop γ g z u ≤ firstLiveRadiusStop γ g z v := by
  by_cases hv : firstLiveRadiusStop γ g z v = (⊤ : ℝ≥0∞)
  · simp only [hv,le_top]
  obtain ⟨t,htau,hzt,hrt⟩ := RadiusPast.live_radius_witness h hU hv
  have hρ : (2*z.im)*Real.exp (-v) ≤ (2*z.im)*Real.exp (-u) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg huv)) (by have hy : 0 < z.im := hz; positivity)
  have hρ0 : (2*z.im)*Real.exp (-u) ≤ loewnerRadius g 0 z := by
    rw [h.radius_initial hz]
    exact mul_le_of_le_one_right (by have hy : 0 < z.im := hz; positivity)
      (Real.exp_le_one_iff.2 (neg_nonpos.2 hu))
  obtain ⟨s,hs,hseq⟩ := intermediate_value_Icc' t.coe_nonneg
    (h.continuous_radius t.coe_nonneg (hU.mono Icc_subset_Ici_self) hzt) ⟨hrt ▸ hρ,hρ0⟩
  have hstop := h.firstLiveRadiusStop_eq hU (t := ⟨s,hs.1⟩) (survivingDomain_mono hs.2 hzt) hseq
  rw [hstop,htau]
  exact ENNReal.coe_le_coe.2 (show (⟨s,hs.1⟩ : ℝ≥0) ≤ t from hs.2)

include h hU in
lemma firstLiveRadiusStop_pos {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u) :
    0 < firstLiveRadiusStop γ g z u := by
  by_cases hv : firstLiveRadiusStop γ g z u = (⊤ : ℝ≥0∞)
  · simp only [hv,ENNReal.zero_lt_top]
  obtain ⟨t,htau,hzt,hrt⟩ := RadiusPast.live_radius_witness h hU hv
  have ht : 0 < t := by
    by_contra hn
    have he : t = 0 := le_antisymm (not_lt.1 hn) zero_le
    rw [he,NNReal.coe_zero,h.radius_initial hz] at hrt
    have hr : (2*z.im)*Real.exp (-u) < 2*z.im :=
      mul_lt_of_lt_one_right (by have hy : 0 < z.im := hz; positivity)
        (Real.exp_lt_one_iff.2 (neg_neg_of_pos hu))
    exact (ne_of_lt hr) hrt.symm
  rw [htau]
  exact ENNReal.coe_pos.2 ht

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

def CompletedStoppedPast {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (τ : Ω → ℝ≥0∞) (A : Set Ω) : Prop :=
  NullMeasurableSet A P ∧ ∀ t : ℝ≥0, ∃ E : Set Ω, MeasurableSet[pastSigma B t] E ∧
    E =ᵐ[P] (A ∩ {sample | τ sample ≤ (t : ℝ≥0∞)} : Set Ω)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable
namespace CompletedStoppedPast
variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {τ σ : Ω → ℝ≥0∞} {A C : Set Ω}

lemma empty : CompletedStoppedPast B P τ ∅ := by
  refine ⟨nullMeasurableSet_empty,fun t => ⟨∅,@MeasurableSet.empty Ω (pastSigma B t),?_⟩⟩
  simp only [empty_inter]
  exact Filter.EventuallyEq.rfl

lemma union (hA : CompletedStoppedPast B P τ A) (hC : CompletedStoppedPast B P τ C) :
    CompletedStoppedPast B P τ (A ∪ C) := by
  refine ⟨hA.1.union hC.1,?_⟩
  intro t
  obtain ⟨E,hE,he⟩ := hA.2 t
  obtain ⟨F,hF,hf⟩ := hC.2 t
  refine ⟨E ∪ F,hE.union hF,?_⟩
  filter_upwards [he,hf] with x he hf
  change (x∈E ∨ x∈F) = ((x∈A ∨ x∈C) ∧ τ x ≤ (t:ℝ≥0∞))
  change (x∈E) = (x∈A ∧ τ x ≤ (t:ℝ≥0∞)) at he
  change (x∈F) = (x∈C ∧ τ x ≤ (t:ℝ≥0∞)) at hf
  rw [he,hf]
  exact propext (by tauto)

lemma diff (hA : CompletedStoppedPast B P τ A) (hC : CompletedStoppedPast B P τ C) :
    CompletedStoppedPast B P τ (A \ C) := by
  refine ⟨hA.1.diff hC.1,?_⟩
  intro t
  obtain ⟨E,hE,he⟩ := hA.2 t
  obtain ⟨F,hF,hf⟩ := hC.2 t
  refine ⟨E \ F,hE.diff hF,?_⟩
  filter_upwards [he,hf] with x he hf
  change (x∈E ∧ x∉F) = ((x∈A ∧ x∉C) ∧ τ x ≤ (t:ℝ≥0∞))
  change (x∈E) = (x∈A ∧ τ x ≤ (t:ℝ≥0∞)) at he
  change (x∈F) = (x∈C ∧ τ x ≤ (t:ℝ≥0∞)) at hf
  rw [he,hf]
  exact propext (by tauto)

lemma mono (hA : CompletedStoppedPast B P τ A)
    (hu : CompletedStoppedPast B P σ univ) (hτσ : ∀ᵐ x ∂P, τ x ≤ σ x) :
    CompletedStoppedPast B P σ A := by
  refine ⟨hA.1,?_⟩
  intro t
  obtain ⟨E,hE,he⟩ := hA.2 t
  obtain ⟨F,hF,hf⟩ := hu.2 t
  refine ⟨E ∩ F,hE.inter hF,?_⟩
  filter_upwards [he,hf,hτσ] with x he hf hle
  change (x∈E ∧ x∈F) = (x∈A ∧ σ x ≤ (t:ℝ≥0∞))
  change (x∈E) = (x∈A ∧ τ x ≤ (t:ℝ≥0∞)) at he
  change (x∈F) = (True ∧ σ x ≤ (t:ℝ≥0∞)) at hf
  rw [he,hf]
  apply propext
  constructor
  · exact fun hh => ⟨hh.1.1,hh.2.2⟩
  · exact fun hh => ⟨⟨hh.1,hle.trans hh.2⟩,⟨trivial,hh.2⟩⟩

end CompletedStoppedPast

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

lemma finiteStoppedDensity_stoppedPast {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 < u)
    (S : Set ℝ≥0∞) (hS : MeasurableSet S) :
    CompletedStoppedPast B P (fun sample => firstLiveRadiusStop (γ sample) (g sample) z u)
      {sample | finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∈ S} := by
  refine ⟨?_,?_⟩
  · exact (finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu).nullMeasurableSet_preimage hS
  intro T
  by_cases ht : T = 0
  · refine ⟨∅,@MeasurableSet.empty Ω (pastSigma B T),?_⟩
    filter_upwards [hmaps,hB.cont] with sample hm hc
    have hp := hm.firstLiveRadiusStop_pos
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) hz hu
    apply propext
    simp only [mem_empty_iff_false,mem_inter_iff,mem_ofPred_eq,ht,ENNReal.coe_zero]
    constructor
    · exact False.elim
    · exact fun hh => (not_le_of_gt hp) hh.2
  have hTp : 0 < (T:ℝ) := by exact_mod_cast pos_iff_ne_zero.2 ht
  let F := RadiusPast.observed κ B hz u hu.le T
  have hFm := RadiusPast.measurable_observed κ B hz u hu.le T hTp
  refine ⟨{sample | 0 < F sample} ∩ F ⁻¹' S,
    (measurableSet_lt measurable_const hFm).inter (hS.preimage hFm),?_⟩
  filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb0
  have he := RadiusPast.observed_eq κ B γ g f sample hm hz hu hc hb0 T hTp
  have hp := RadiusPast.byTime_pos_iff κ B γ g f sample hm hz u hc T
  apply propext
  change (0 < F sample ∧ F sample ∈ S) ↔
    (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∈ S ∧
      firstLiveRadiusStop (γ sample) (g sample) z u ≤ (T:ℝ≥0∞))
  change F sample = _ at he
  rw [he,hp]
  by_cases hh : firstLiveRadiusStop (γ sample) (g sample) z u ≤ (T:ℝ≥0∞)
  · simp only [RadiusPast.byTime,hh,ite_true,true_and,and_true]
  · simp only [hh,false_and,and_false]

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace CompletedStoppedPast
variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {τ : Ω → ℝ≥0∞}

lemma finsetUnion {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, CompletedStoppedPast B P τ (A i)) :
    CompletedStoppedPast B P τ (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] using (empty (B:=B) (P:=P) (τ:=τ))
  | @insert a s ha ih =>
    simpa only [Finset.set_biUnion_insert] using
      (hA a (Finset.mem_insert_self _ _)).union (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))

end CompletedStoppedPast

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace FiniteFirstEvents
variable {Ω ι : Type*} [LinearOrder ι]

def first (s : Finset ι) (A : ι → Set Ω) (i : ι) : Set Ω :=
  A i \ ⋃ j ∈ s.filter (fun j => j < i), A j

lemma first_subset (s : Finset ι) (A : ι → Set Ω) (i : ι) : first s A i ⊆ A i :=
  sdiff_subset

lemma first_disjoint (s : Finset ι) (A : ι → Set Ω) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) : Disjoint (first s A i) (first s A j) := by
  classical
  apply Set.disjoint_left.2
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hxj.2 (mem_iUnion.2 ⟨i,mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨hi,hij⟩,hxi.1⟩⟩)
  · exact hxi.2 (mem_iUnion.2 ⟨j,mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨hj,hji⟩,hxj.1⟩⟩)

lemma union_first (s : Finset ι) (A : ι → Set Ω) :
    (⋃ i ∈ s, first s A i) = ⋃ i ∈ s, A i := by
  classical
  apply Subset.antisymm
  · exact iUnion₂_mono (fun i _ => first_subset s A i)
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.1 hx
    let t := s.filter (fun i => x ∈ A i)
    have ht : t.Nonempty := ⟨i,Finset.mem_filter.2 ⟨hi,hxi⟩⟩
    let j := t.min' ht
    have hj := Finset.mem_filter.1 (Finset.min'_mem t ht)
    apply mem_iUnion₂.2 ⟨j,hj.1,?_⟩
    refine ⟨hj.2,?_⟩
    intro hbad
    obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.1 hbad
    have hkj := (Finset.mem_filter.1 hk).2
    have hjk := Finset.min'_le t k (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hk).1,hxk⟩)
    exact (not_lt_of_ge hjk) hkj

lemma first_stoppedPast [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {τ : Ω → ℝ≥0∞}
    (s : Finset ι) (A : ι → Set Ω) (i : ι)
    (hi : CompletedStoppedPast B P τ (A i))
    (hj : ∀ j ∈ s, j < i → CompletedStoppedPast B P τ (A j)) :
    CompletedStoppedPast B P τ (first s A i) := by
  classical
  exact hi.diff (CompletedStoppedPast.finsetUnion (s.filter (fun j => j < i)) A
    (fun j hj' => hj j (Finset.mem_filter.1 hj').1 (Finset.mem_filter.1 hj').2))

end FiniteFirstEvents

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

lemma finiteCenteredMeasure_event_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (A : Set Ω)
    (hA : CompletedStoppedPast B P (fun sample => firstLiveRadiusStop (γ sample) (g sample) z u) A)
    (K : ℝ≥0∞)
    (hb : ∀ᵐ sample ∂P.restrict A,
      finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ≤ K) :
    finiteCenteredMeasure κ P B γ g z v A ≤
      (ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)))⁻¹ * K * P A := by
  have he := finiteStoppedDensity_consistent κ hκ B hB γ g f hγ hmaps z hz u v hu huv A hA.1 hA.2
  have hm0 : ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (localizationInitialGreen_pos κ hz)).ne'
  rw [finiteCenteredMeasure,withDensity_apply₀ _ hA.1]
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0),he,mul_assoc]
  apply mul_le_mul' le_rfl
  exact (lintegral_mono_ae hb).trans_eq (by rw [lintegral_const,Measure.restrict_apply_univ])

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteFirstEvents

def densityBelow {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) (K : ℝ≥0∞) : Set Ω :=
  {sample | finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∈ Ioo 0 K}

lemma finiteCentered_grid_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (v : ℝ) (s : Finset ℚ)
    (hs : ∀ q ∈ s, 0 < (q:ℝ) ∧ (q:ℝ) ≤ v)
    (a : ℚ → ℝ≥0∞) (K : ℝ≥0∞) (ha : ∀ q ∈ s, a q ≤ K) :
    finiteCenteredMeasure κ P B γ g z v (⋃ q ∈ s, densityBelow κ B γ g z q (a q)) ≤
      (ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)))⁻¹ * K *
        P (⋃ q ∈ s, densityBelow κ B γ g z q (a q)) := by
  classical
  let A := fun q : ℚ => densityBelow κ B γ g z q (a q)
  let Q := finiteCenteredMeasure κ P B γ g z v
  let k := (ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)))⁻¹ * K
  have hpast (q : ℚ) (hq : q ∈ s) : CompletedStoppedPast B P
      (fun sample => firstLiveRadiusStop (γ sample) (g sample) z q) (A q) :=
    finiteStoppedDensity_stoppedPast κ hκ B hB γ g f hmaps z hz q (hs q hq).1 (Ioo 0 (a q)) measurableSet_Ioo
  have huniv (q : ℚ) (hq : q ∈ s) : CompletedStoppedPast B P
      (fun sample => firstLiveRadiusStop (γ sample) (g sample) z q) univ := by
    simpa only [mem_univ,ofPred_true] using
      finiteStoppedDensity_stoppedPast κ hκ B hB γ g f hmaps z hz q (hs q hq).1 univ MeasurableSet.univ
  have hfirst (q : ℚ) (hq : q∈s) : CompletedStoppedPast B P
      (fun sample => firstLiveRadiusStop (γ sample) (g sample) z q) (first s A q) := by
    apply first_stoppedPast s A q (hpast q hq)
    intro j hj hjq
    apply (hpast j hj).mono (huniv q hq)
    filter_upwards [hmaps,hB.cont] with sample hm hc
    exact hm.firstLiveRadiusStop_mono
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) hz (hs j hj).1.le
      (by exact_mod_cast hjq.le)
  have hle (q : ℚ) (hq : q∈s) : Q (first s A q) ≤ k * P (first s A q) := by
    apply finiteCenteredMeasure_event_le κ hκ B hB γ g f hγ hmaps z hz q v
      (hs q hq).1.le (hs q hq).2 (first s A q) (hfirst q hq) K
    filter_upwards [ae_restrict_mem₀ (hfirst q hq).1] with sample hx
    exact hx.1.2.le.trans (ha q hq)
  have hdis : PairwiseDisjoint (↑s : Set ℚ) (first s A) :=
    fun i hi j hj hij => first_disjoint s A hi hj hij
  have hPQ : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hsumQ : Q (⋃ q∈s,first s A q) = ∑ q∈s,Q (first s A q) :=
    measure_biUnion_finset₀ hdis.aedisjoint (fun q hq => (hfirst q hq).1.mono_ac hPQ)
  have hsumP : P (⋃ q∈s,first s A q) = ∑ q∈s,P (first s A q) :=
    measure_biUnion_finset₀ hdis.aedisjoint (fun q hq => (hfirst q hq).1)
  change Q (⋃ q∈s,A q) ≤ k * P (⋃ q∈s,A q)
  rw [← union_first s A,hsumQ,hsumP]
  calc
    _ ≤ ∑ q∈s,k*P (first s A q) := Finset.sum_le_sum hle
    _ = _ := by rw [Finset.mul_sum]

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma finiteCentered_countableGrid_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (v : ℝ) (J : Set ℚ)
    (hJ : ∀ q ∈ J, 0 < (q:ℝ) ∧ (q:ℝ) ≤ v)
    (a : ℚ → ℝ≥0∞) (K : ℝ≥0∞) (ha : ∀ q ∈ J, a q ≤ K) :
    finiteCenteredMeasure κ P B γ g z v (⋃ q ∈ J, densityBelow κ B γ g z q (a q)) ≤
      (ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)))⁻¹ * K *
        P (⋃ q ∈ J, densityBelow κ B γ g z q (a q)) := by
  classical
  let A := fun q : ℚ => densityBelow κ B γ g z q (a q)
  let F := fun s : Finset ℚ => ⋃ q ∈ s.filter (fun q => q∈J), A q
  have hm : Monotone F := by
    intro s t hst
    exact iUnion₂_mono' (fun q hq => ⟨q, Finset.mem_filter.2
      ⟨hst (Finset.mem_filter.1 hq).1,(Finset.mem_filter.1 hq).2⟩,Subset.rfl⟩)
  have he : (⋃ s, F s) = ⋃ q ∈ J, A q := by
    ext sample
    simp only [F,mem_iUnion,Finset.mem_filter]
    constructor
    · rintro ⟨s,q,⟨hq,hJq⟩,hx⟩
      exact ⟨q,hJq,hx⟩
    · rintro ⟨q,hq,hx⟩
      exact ⟨{q},q,⟨Finset.mem_singleton_self q,hq⟩,hx⟩
  have hsub (s : Finset ℚ) : F s ⊆ ⋃ q ∈ J,A q := by
    rw [← he]
    exact subset_iUnion F s
  change finiteCenteredMeasure κ P B γ g z v (⋃ q∈J,A q) ≤ _
  rw [← he,hm.measure_iUnion]
  apply iSup_le
  intro s
  apply (finiteCentered_grid_le κ hκ B hB γ g f hγ hmaps z hz v
    (s.filter (fun q => q∈J))
    (fun q hq => hJ q (Finset.mem_filter.1 hq).2) a K
    (fun q hq => ha q (Finset.mem_filter.1 hq).2)).trans
  exact mul_le_mul' le_rfl (measure_mono (he ▸ hsub s))

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace FiniteClock

def angleFloor (δ u : ℝ) : ℝ := δ * Real.exp (-u/8)

def threshold (κ : ℝ) (z : ℂ) (δ u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-codimension κ) * (angleFloor δ u)^(8/κ-1))

def blockThreshold (κ : ℝ) (z : ℂ) (δ n : ℝ) : ℝ :=
  (2*z.im)^(-codimension κ) * Real.exp (codimension κ*(n+1)) *
    δ^(8/κ-1) * Real.exp (-(8/κ-1)*n/8)

lemma exponent_pos {κ : ℝ} (hκ : 0 < κ ∧ κ < 8) : 0 < 8/κ-1 := by
  have h : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by linarith)
  linarith

lemma codimension_pos {κ : ℝ} (hκ : 0 < κ ∧ κ < 8) : 0 < codimension κ := by
  unfold codimension dimension
  linarith

lemma angleFloor_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 < angleFloor δ u := by
  unfold angleFloor
  positivity

lemma threshold_formula (κ : ℝ) {z : ℂ} (hz : z ∈ halfPlane) {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    threshold κ z δ u = ENNReal.ofReal
      ((2*z.im)^(-codimension κ) * Real.exp (codimension κ*u) *
        δ^(8/κ-1) * Real.exp (-(8/κ-1)*u/8)) := by
  have hy : 0 < 2*z.im := by have : 0 < z.im := hz; positivity
  unfold threshold angleFloor
  rw [Real.mul_rpow hy.le (Real.exp_pos _).le,Real.mul_rpow hδ.le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul]
  congr 1
  rw [show -u * -codimension κ = codimension κ*u by ring,
    show (-u/8)*(8/κ-1) = -(8/κ-1)*u/8 by ring]
  ring

lemma threshold_le_block (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {z : ℂ} (hz : z ∈ halfPlane) {δ : ℝ} (hδ : 0 < δ)
    {n u : ℝ} (hnu : n ≤ u) (hun : u ≤ n+1) :
    threshold κ z δ u ≤ ENNReal.ofReal (blockThreshold κ z δ n) := by
  rw [threshold_formula κ hz hδ]
  apply ENNReal.ofReal_le_ofReal
  unfold blockThreshold
  have hy : 0 < 2*z.im := by have : 0 < z.im := hz; positivity
  have hp := codimension_pos hκ
  have ha := exponent_pos hκ
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hδ _).le
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hun hp.le))
      (Real.rpow_pos_of_pos hy _).le
  · apply Real.exp_le_exp.2
    nlinarith
  · positivity
  · positivity

lemma block_cancel (κ C δ n : ℝ) {z : ℂ} (hz : z ∈ halfPlane) :
    ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))⁻¹ *
      blockThreshold κ z δ n *
      (C*Real.exp (-codimension κ*n)*(z.im/‖z‖)^(8/κ-1)) =
      C * Real.exp (codimension κ) * δ^(8/κ-1) * Real.exp (-(8/κ-1)*n/8) := by
  have hy : 0 < 2*z.im := by have : 0 < z.im := hz; positivity
  have hs := Real.rpow_pos_of_pos (FiniteTilt.initial_sine_pos hz) (8/κ-1)
  have hp := Real.rpow_pos_of_pos hy (-codimension κ)
  have he : Real.exp (codimension κ*(n+1))*Real.exp (-codimension κ*n) = Real.exp (codimension κ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold blockThreshold
  field_simp
  simp only [neg_mul] at he
  linear_combination δ^(8/κ-1)*C * he

def blockIndex (v : ℝ) (n : ℕ) : Set ℚ :=
  {q | 0 < (q:ℝ) ∧ (q:ℝ) ≤ v ∧ (n:ℝ) ≤ (q:ℝ) ∧ (q:ℝ) ≤ (n:ℝ)+1}

def blockBad {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (δ v : ℝ) (n : ℕ) : Set Ω :=
  ⋃ q ∈ blockIndex v n, densityBelow κ B γ g z q (threshold κ z δ q)

lemma blockBad_subset_hit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (δ v : ℝ) (n : ℕ) :
    blockBad κ B γ g z δ v n ≤ᵐ[P]
      {sample | firstLiveRadiusStop (γ sample) (g sample) z n ≠ (⊤ : ℝ≥0∞)} := by
  filter_upwards [hmaps,hB.cont] with sample hm hc hx
  rcases mem_iUnion.1 hx with ⟨q,hq⟩
  rcases mem_iUnion.1 hq with ⟨hq,hx⟩
  have hhit : firstLiveRadiusStop (γ sample) (g sample) z q ≠ (⊤ : ℝ≥0∞) := by
    intro he
    have hh := hx.1
    simp only [finiteStoppedDensity,he,ite_true,lt_self_iff_false] at hh
  have hh := hm.firstLiveRadiusStop_mono
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) hz
    (Nat.cast_nonneg n) hq.2.2.1
  exact ne_top_of_le_ne_top hhit hh

lemma ordinary_natural_radius_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      P {sample | firstLiveRadiusStop (γ sample) (g sample) z n ≠ (⊤ : ℝ≥0∞)} ≤
        ENNReal.ofReal (C*Real.exp (-codimension κ*n)*(z.im/‖z‖)^(8/κ-1)) := by
  obtain ⟨C,hC,hbound⟩ := radiusApproachBound κ hκ
  let S := (z.im/‖z‖)^(8/κ-1)
  have hS : 0 < S := Real.rpow_pos_of_pos (FiniteTilt.initial_sine_pos hz) _
  refine ⟨C+S⁻¹,by positivity,?_⟩
  intro n
  cases n with
  | zero =>
    simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
    apply (prob_le_one).trans
    apply ENNReal.one_le_ofReal.2
    change 1 ≤ (C+S⁻¹)*S
    rw [add_mul,inv_mul_cancel₀ hS.ne']
    linarith [mul_pos hC hS]
  | succ n =>
    simp only [Nat.cast_add,Nat.cast_one]
    apply (hbound P B hB γ g f hγ hmaps z hz (n+1)
      (by norm_num)).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (inv_nonneg.2 hS.le))
        (Real.exp_pos _).le) hS.le

lemma block_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (C : ℝ) (_hC : 0 < C)
    (hbound : ∀ n : ℕ,
      P {sample | firstLiveRadiusStop (γ sample) (g sample) z n ≠ (⊤ : ℝ≥0∞)} ≤
        ENNReal.ofReal (C*Real.exp (-codimension κ*n)*(z.im/‖z‖)^(8/κ-1)))
    (δ : ℝ) (hδ : 0 < δ) (v : ℝ) (n : ℕ) :
    finiteCenteredMeasure κ P B γ g z v (blockBad κ B γ g z δ v n) ≤
      ENNReal.ofReal (C * Real.exp (codimension κ) * δ^(8/κ-1) *
        Real.exp (-(8/κ-1)*n/8)) := by
  have hm0 := localizationInitialGreen_pos κ hz
  have hy : 0 < 2*z.im := by have : 0 < z.im := hz; positivity
  have hK : 0 < blockThreshold κ z δ n := by
    unfold blockThreshold
    positivity
  have hp := (measure_mono_ae (blockBad_subset_hit κ B hB γ g f hmaps z hz δ v n)).trans (hbound n)
  have hg := finiteCentered_countableGrid_le κ hκ B hB γ g f hγ hmaps z hz v
    (blockIndex v n) (fun q hq => ⟨hq.1,hq.2.1⟩)
    (fun q => threshold κ z δ q) (ENNReal.ofReal (blockThreshold κ z δ n))
    (fun q hq => threshold_le_block κ hκ hz hδ hq.2.2.1 hq.2.2.2)
  apply hg.trans
  apply (mul_le_mul' le_rfl hp).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_mul (inv_nonneg.2 hm0.le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hm0.le) hK.le)]
  rw [block_cancel κ C δ n hz]

end FiniteClock

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.FiniteClock

def bad {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (δ v : ℝ) : Set Ω :=
  ⋃ n : ℕ, blockBad κ B γ g z δ v n

lemma mem_bad_of_rational {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (δ v : ℝ)
    (q : ℚ) (hq : 0 < (q:ℝ)) (hqv : (q:ℝ) ≤ v) {sample : Ω}
    (hx : sample ∈ densityBelow κ B γ g z q (threshold κ z δ q)) :
    sample ∈ bad κ B γ g z δ v := by
  apply mem_iUnion.2 ⟨⌊(q:ℝ)⌋₊,?_⟩
  apply mem_iUnion.2 ⟨q,?_⟩
  apply mem_iUnion.2 ⟨⟨hq,hqv,Nat.floor_le hq.le,(Nat.lt_floor_add_one (q:ℝ)).le⟩,hx⟩

lemma geometric_blocks (κ C δ : ℝ) (hκ : 0 < κ ∧ κ < 8) (hC : 0 < C) (hδ : 0 < δ) :
    (∑' n : ℕ, ENNReal.ofReal (C*Real.exp (codimension κ)*δ^(8/κ-1)*Real.exp (-(8/κ-1)*n/8))) =
      ENNReal.ofReal ((C*Real.exp (codimension κ)/(1-Real.exp (-(8/κ-1)/8)))*δ^(8/κ-1)) := by
  have ha := exponent_pos hκ
  have hr : Real.exp (-(8/κ-1)/8) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have he (n : ℕ) : Real.exp (-(8/κ-1)*n/8) = (Real.exp (-(8/κ-1)/8))^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he,ENNReal.ofReal_mul (show 0≤C*Real.exp (codimension κ)*δ^(8/κ-1) by positivity),
    ENNReal.ofReal_pow (Real.exp_pos _).le]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric,← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (Real.exp_pos _).le,← ENNReal.ofReal_inv_of_pos (sub_pos.2 hr),
    ← ENNReal.ofReal_mul (show 0≤C*Real.exp (codimension κ)*δ^(8/κ-1) by positivity)]
  congr 1
  ring

lemma bad_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → ∀ v : ℝ,
      finiteCenteredMeasure κ P B γ g z v (bad κ B γ g z δ v) ≤ ENNReal.ofReal (D*δ^(8/κ-1)) := by
  obtain ⟨C,hC,hbound⟩ := ordinary_natural_radius_bound κ hκ B hB γ g f hγ hmaps z hz
  have hr : Real.exp (-(8/κ-1)/8) < 1 := Real.exp_lt_one_iff.2 (by have := exponent_pos hκ; linarith)
  refine ⟨C*Real.exp (codimension κ)/(1-Real.exp (-(8/κ-1)/8)),by positivity,?_⟩
  intro δ hδ v
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum (fun n => block_bound κ hκ B hB γ g f hγ hmaps z hz C hC hbound δ hδ v n)).trans_eq
  exact geometric_blocks κ C δ hκ hC hδ

lemma exists_small_floor {a D ε : ℝ} (ha : 0 < a) (hD : 0 < D) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ D*δ^a < ε := by
  have hp : 0 < ε/(2*D) := by positivity
  refine ⟨(ε/(2*D))^(1/a),Real.rpow_pos_of_pos hp _,?_⟩
  rw [← Real.rpow_mul hp.le,one_div_mul_cancel ha.ne',Real.rpow_one]
  have he : D*(ε/(2*D)) = ε/2 := by field_simp
  rw [he]
  linarith

lemma rational_clock_nonneg {T v : ℝ} {C F : ℝ → ℝ}
    (hT : 0 < T) (hC : ContinuousOn C (Icc 0 T)) (hCs : StrictMonoOn C (Icc 0 T))
    (hC0 : C 0 = 0) (hCT : C T = v) (hF : ContinuousOn F (Icc 0 T))
    (hrat : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) ≤ v →
      ∀ s ∈ Icc 0 T, C s = (q:ℝ) → 0 ≤ F s) :
    ∀ t ∈ Ioo 0 T, 0 ≤ F t := by
  intro t ht
  by_contra hn
  have hneg : F t < 0 := lt_of_not_ge hn
  have hFc : ContinuousAt F t := (hF t ⟨ht.1.le,ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2)
  have he : ∀ᶠ s in 𝓝 t, F s < 0 := hFc.tendsto.eventually (gt_mem_nhds hneg)
  obtain ⟨e,he0,he⟩ := Metric.eventually_nhds_iff.1 he
  have hlow : max 0 (t-e) < t := max_lt ht.1 (by linarith)
  obtain ⟨a,ha,hat⟩ := exists_between hlow
  have ha0 : 0 < a := (le_max_left 0 (t-e)).trans_lt ha
  have hae : t-e < a := (le_max_right 0 (t-e)).trans_lt ha
  have haq : a ∈ Icc 0 T := ⟨ha0.le,(hat.trans ht.2).le⟩
  obtain ⟨q,hqa,hqt⟩ := exists_rat_btwn (hCs haq ⟨ht.1.le,ht.2.le⟩ hat)
  have hq0 : 0 < (q:ℝ) := by
    have hc := hCs ⟨le_rfl,hT.le⟩ haq ha0
    rw [hC0] at hc
    exact hc.trans hqa
  have hqv : (q:ℝ) ≤ v := by
    have hc := hCs.monotoneOn ⟨ht.1.le,ht.2.le⟩ ⟨hT.le,le_rfl⟩ ht.2.le
    rw [hCT] at hc
    exact hqt.le.trans hc
  obtain ⟨s,hs,hsq⟩ := intermediate_value_Icc hat.le
    (hC.mono (Icc_subset_Icc haq.1 ht.2.le)) ⟨hqa.le,hqt.le⟩
  have hst : s ∈ Icc 0 T := ⟨ha0.le.trans hs.1,hs.2.trans ht.2.le⟩
  have hsn : F s < 0 := he (by
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.2 hs.2)]
    linarith [hs.1])
  exact (not_lt_of_ge (hrat q hq0 hqv s hst hsq)) hsn

end SLEExactGauge.FiniteClock

end

end

end OAI
