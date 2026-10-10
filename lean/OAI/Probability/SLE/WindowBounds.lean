import Mathlib
import OAI.Probability.SLE.PhysicalKernelUtilities
import OAI.Probability.SLE.WindowGeometry

namespace OAI

/-! Window Bounds for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance windowBoundsPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_liveTime_eq_sphere_of_finite {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) (hn : liveSpatialHitTime γ z r ≠ ⊤) :
    liveSpatialHitTime γ z r = spatialHitTime γ z r := by
  have he := source_liveTime_eq_killed hc z r hs
  split_ifs at he with hl
  · exact he
  · exact (hn he).elim

lemma source_windowV_stopped_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ) (κ : ℝ) (z : ℂ) (r ε R : ℝ)
    (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    spatialGreenWeight κ U γ G z ε * sourceSpatialWindowH γ z r ε R =
      greenDensity κ U γ G (sourceSpatialWindowTime γ z r ε R).untopA z *
        sourceSpatialWindowH γ z r ε R := by
  by_cases hH : sourceSpatialWindowH γ z r ε R = 1
  · obtain ⟨he,hn⟩ := (source_windowH_iff hc z r ε R her hs).mp hH
    have hr := source_liveTime_eq_sphere_of_finite hc z ε (her.trans hs) hn
    have hraw : spatialHitTime γ z ε ≠ ⊤ := hr ▸ hn
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hraw
    rw [hH, mul_one, mul_one, he, hr, spatialGreenWeight, ite_eq_right hraw, ← ht]
    rfl
  · have hz : sourceSpatialWindowH γ z r ε R = 0 := by
      unfold sourceSpatialWindowH at hH ⊢
      split_ifs <;> simp_all
    rw [hz,mul_zero,mul_zero]

lemma source_windowV_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ) (her : ε ≤ r) (hy : r ≤ z.im)
    (hτ : IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R)) :
    Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε *
        sourceSpatialWindowH (γ ω) z r ε R) := by
  have hg := measurable_stoppedValue
    (source_killedGreen_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have hH := (source_windowHB_stopped_measurable a z r ε R hτ).1
  convert hg.mul hH using 1 <;> try rfl
  funext ω
  apply source_windowV_stopped_eq (a.trace_continuous ω) _ _ _ _ _ _ _ her
  rw [(a.witness ω).2.1,dist_zero_left]
  exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm _))

lemma source_liveWeight_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r : ℝ) (hy : r ≤ z.im)
    (hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r)) :
    Measurable[hσ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) := by
  have hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  apply hm.mono (hraw.measurableSpace_mono hσ ?_) le_rfl
  intro ω
  have hs : r ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1,dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm _))
  change spatialHitTime (γ ω) z r ≤ liveSpatialHitTime (γ ω) z r
  rw [source_liveTime_eq_killed (a.trace_continuous ω) z r hs]
  split_ifs <;> first | exact le_rfl | exact le_top

lemma source_collarHB_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarH D (γ p.2) p.1 r ε R) ∧
    Measurable (fun p : ℂ × a.samples => sourceCollarB D (γ p.2) p.1 r ε R) := by
  let τ := fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R
  have ht : Measurable τ := source_collarFinish_joint a D hD r ε R hy
  have hg : Measurable (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ))) :=
    (source_tracePath_measurable a).comp measurable_snd
  have hl := source_joint_survival_measurable
    (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ)))
    (fun p => (τ p).untopD 0) Prod.fst hg (ht.untopD 0) measurable_fst
  have hd : Measurable (fun p : ℂ × a.samples => dist (γ p.2 ((τ p).untopD 0)) p.1) :=
    (continuous_eval.measurable.comp (hg.prodMk (ht.untopD 0))).dist measurable_fst
  have hn : MeasurableSet {p | τ p ≠ ⊤} := (measurableSet_eq_fun ht measurable_const).compl
  have hH : Measurable (fun p : ℂ × a.samples =>
      if τ p ≠ ⊤ ∧ p.1 ∈ survivingDomain (γ p.2) ((τ p).untopD 0) ∧
      dist (γ p.2 ((τ p).untopD 0)) p.1 ≤ ε then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le hd measurable_const))) measurable_const measurable_const
  have hB : Measurable (fun p : ℂ × a.samples =>
      if τ p ≠ ⊤ ∧ p.1 ∈ survivingDomain (γ p.2) ((τ p).untopD 0) ∧
      R ≤ dist (γ p.2 ((τ p).untopD 0)) p.1 then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le measurable_const hd))) measurable_const measurable_const
  constructor
  · convert hH using 1
    funext p
    by_cases hz : p.1 ∈ D
    · simp only [sourceCollarH,sourceSpatialWindowH,τ,sourceCollarFinish,ite_eq_left hz]
    · simp only [sourceCollarH,τ,sourceCollarFinish,ite_eq_right hz,ne_eq,not_true_eq_false,false_and,ite_false]
  · convert hB using 1
    funext p
    by_cases hz : p.1 ∈ D
    · simp only [sourceCollarB,sourceSpatialWindowB,τ,sourceCollarFinish,ite_eq_left hz]
    · simp only [sourceCollarB,τ,sourceCollarFinish,ite_eq_right hz,ne_eq,not_true_eq_false,false_and,ite_false]

lemma source_stop_space_congr {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (he : σ = τ) :
    hσ.measurableSpace = hτ.measurableSpace := by
  subst τ
  rfl

lemma source_collarHBV_stopped
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r ε R : ℝ) (her : ε ≤ r) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    let hτ := source_collarFinish_stopping a D r ε R hy z
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceCollarH D (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceCollarB D (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε *
        sourceCollarH D (γ ω) z r ε R) := by
  dsimp only
  by_cases hz : z ∈ D
  · have ht := source_window_stopping a z r ε R (hy z hz)
    have hh := source_windowHB_stopped_measurable a z r ε R ht
    have hv := source_windowV_stopped_measurable a z r ε R her (hy z hz) ht
    have hspace := source_stop_space_congr (source_collarFinish_stopping a D r ε R hy z) ht
      (funext fun ω => by simp only [sourceCollarFinish,ite_eq_left hz])
    rw [hspace]
    simpa only [sourceCollarH,sourceCollarB,ite_eq_left hz] using And.intro hh.1 (And.intro hh.2 hv)
  · simp only [sourceCollarH,sourceCollarB,ite_eq_right hz,mul_zero]
    exact ⟨measurable_const,measurable_const,measurable_const⟩

lemma source_collarWeight_stopped
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    Measurable[(source_collarStart_stopping a D r hy z).measurableSpace] (fun ω : a.samples =>
      if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r else 0) := by
  by_cases hz : z ∈ D
  · have hs := source_liveHit_stopping a z r (hy z hz)
    have hw := source_liveWeight_stopped_measurable a z r (hy z hz) hs
    have hspace := source_stop_space_congr (source_collarStart_stopping a D r hy z) hs
      (funext fun ω => by simp only [sourceCollarStart,ite_eq_left hz])
    rw [hspace]
    simpa only [ite_eq_left hz] using hw
  · simp only [ite_eq_right hz]
    exact measurable_const

 theorem sourceSpatialWindowMeasurable_proved : SourceSpatialWindowMeasurableTarget := by
  intro Ω m P κ hκ hκ8 γ a D hD ε r R hε her hrR hy
  dsimp only
  refine ⟨⟨source_collarStart_stopping a D r hy,
    source_collarFinish_stopping a D r ε R hy,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · exact source_collarHBV_stopped a D r ε R her.le hy
  · exact source_collarWeight_stopped a D r hy
  · exact source_collarStart_joint a D hD r hy
  · exact source_collarFinish_joint a D hD r ε R hy
  · exact (source_collarHB_joint a D hD r ε R hy).1
  · exact (source_collarHB_joint a D hD r ε R hy).2
  · exact (a.spatialGreenWeight_measurable ε).mul (source_collarHB_joint a D hD r ε R hy).1

end
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_liveIndicator_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε : ℝ) (hy : ε ≤ z.im) :
    Measurable (fun ω : a.samples =>
      if liveSpatialHitTime (γ ω) z ε = ⊤ then (0 : ℝ) else 1) := by
  classical
  have hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z ε) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z ε
  have hK := measurable_stoppedValue
    (source_killedChart_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have hKm : Measurable (fun ω : a.samples =>
      (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
        then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ)) :=
    hK.mono hτ.measurableSpace_le le_rfl
  have htop : MeasurableSet {ω : a.samples | spatialHitTime (γ ω) z ε = ⊤} :=
    measurableSet_eq_fun (hτ.measurable.mono hτ.measurableSpace_le le_rfl) measurable_const
  have hl : MeasurableSet {ω : a.samples |
      0 < (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
        then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ).im} :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp hKm)
  have hmo : Measurable (fun ω : a.samples =>
      if spatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else
        if 0 < (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
          then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ).im then 1 else 0) :=
    Measurable.ite htop measurable_const (Measurable.ite hl measurable_const measurable_const)
  convert hmo using 1
  funext ω
  have hs : ε ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  rw [liveSpatialHitTime_eq (a.trace_continuous ω) z ε hs]
  by_cases ht : spatialHitTime (γ ω) z ε = ⊤
  · simp only [ite_eq_left ht, ite_true]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [ite_eq_right ht, ite_eq_right ht, ← hv]
    change (if (if z ∈ survivingDomain (γ ω) v then (v : WithTop ℝ≥0) else ⊤) = ⊤
      then (0:ℝ) else 1) =
      (if 0 < (if z ∈ survivingDomain (γ ω) v then a.G ω v z else 0 : ℂ).im then 1 else 0)
    by_cases hz : z ∈ survivingDomain (γ ω) v
    · simp only [ite_eq_left hz, WithTop.coe_ne_top, ite_false,
        ite_eq_left ((a.witness ω).imag_positive v z hz)]
    · simp only [ite_eq_right hz, ite_true, Complex.zero_im, lt_self_iff_false, ite_false]

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsApproachPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance windowBoundsApproachPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

noncomputable def sourceApproachConstant (κ : ℝ) : ℝ :=
  (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
    (512 * Real.pi) ^ codimension κ

lemma sourceApproachConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < sourceApproachConstant κ := by
  exact mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by positivity) _)

lemma source_kernel_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    (ζ : ℂ) (hζ : ζ ∈ upperHalfPlane) (ε r R : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (hy : 8 * ε ≤ r)
    (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (hR : 0 < R) (hRb : R ≤ (128 * Real.pi) * r) :
    (∫ p, sourceApproachKernel ε r (ζ, p) ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) ≤
      sourceApproachConstant κ * ε ^ codimension κ *
        (R ^ (-codimension κ) * (Real.sin (Complex.arg ζ)) ^ greenExponent κ) := by
  have hypos : 0 < ζ.im := hζ
  let δ := 8 * ζ.im * ε / r
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδy : δ ≤ ζ.im := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hy (show 0 ≤ ζ.im from hζ.le)]
  have hδsmall : 1 ≤ Real.log ((2 * ζ.im) / ((128 * Real.pi) * δ)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < (128 * Real.pi) * δ)).mpr
    calc
      Real.exp 1 * ((128 * Real.pi) * δ) =
          (2 * ζ.im) * (Real.exp 1 * (512 * Real.pi) * ε) / r := by dsimp [δ]; ring
      _ ≤ (2 * ζ.im) * r / r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by positivity)) hr.le
      _ = 2 * ζ.im := mul_div_cancel_right₀ _ hr.ne'
  have hb := euclidean_approach hB κ hκ hκ8 γ G F (Eventually.of_forall hw)
    ζ hζ δ hδ hδy hδsmall
  let S : Set Ω := {ω | ∃ t : ℝ≥0, dist (γ ω t) ζ < δ}
  have hS : MeasurableSet S := by
    have hh := measurableSet_lt (measurable_const (a := (0:ℝ)))
      ((sourceApproachKernel_measurable ε r).comp ((measurable_const (a := ζ)).prodMk hgm))
    convert hh using 1
    ext ω
    change (∃ t : ℝ≥0, dist (γ ω t) ζ < δ) ↔ 0 <
      (if ∃ t : ℝ≥0, dist (γ ω t) ζ < δ then (1:ℝ) else 0)
    split_ifs <;> simp_all
  have hint : (∫ p, sourceApproachKernel ε r (ζ, p)
      ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) = (P S).toReal := by
    have hfun : Measurable (fun p : C(ℝ≥0, ℂ) => sourceApproachKernel ε r (ζ, p)) :=
      (sourceApproachKernel_measurable ε r).comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫ ω, sourceApproachKernel ε r (ζ, sourceTracePath γ (fun ω => (hw ω).1) ω) ∂P :=
        integral_map hgm.aemeasurable hfun.aestronglyMeasurable
      _ = _ := ?_

    change (∫ ω, S.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    simp only [integral_indicator_const _ hS, smul_eq_mul, mul_one, measureReal_def]
  rw [hint]
  apply hb.trans
  have hsin : 0 ≤ Real.sin (Complex.arg ζ) := by
    rw [Complex.sin_arg]
    exact div_nonneg hζ.le (norm_nonneg _)
  have hC : 0 ≤ uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ :=
    (mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
      (Real.rpow_pos_of_pos (by positivity) _)).le
  have hp : (4 * R / r) ^ codimension κ ≤ (512 * Real.pi) ^ codimension κ := by
    apply Real.rpow_le_rpow (by positivity) _ (codimension_pos κ hκ8).le
    apply (div_le_iff₀ hr).mpr
    nlinarith [hRb]
  have heq := source_rpow_scale (codimension κ) ζ.im ε r R hζ hε hr hR
  dsimp only [initialGreen, δ]
  calc
    _ = (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((2 * ζ.im) ^ (-codimension κ) * (8 * ζ.im * ε / r) ^ codimension κ) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by ring
    _ = (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((4 * R / r) ^ codimension κ * ε ^ codimension κ * R ^ (-codimension κ)) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by rw [heq]
    _ ≤ (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((512 * Real.pi) ^ codimension κ * ε ^ codimension κ * R ^ (-codimension κ)) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by
      gcongr
    _ = _ := by dsimp [sourceApproachConstant]; ring

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_liveSpatialHitTime_ne_top_iff (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    liveSpatialHitTime γ z r ≠ ⊤ ↔
      ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r := by
  simp only [liveSpatialHitTime]
  split_ifs with h
  · simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_iff]
    exact h
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h

 

lemma source_live_contact_restarts
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (τ : ℝ≥0) (hτ : spatialHitTime γ z r = τ)
    (s : ℝ≥0) (hs : z ∈ survivingDomain γ s) (hd : dist (γ s) z ≤ ε) :
    τ < s ∧ z ∈ survivingDomain γ τ ∧ γ s ∈ survivingDomain γ τ ∧
      dist (G τ (γ s) - (U τ : ℂ)) (G τ z - (U τ : ℂ)) <
        8 * (G τ z).im * ε / r := by
  have hs0 : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have her : ε < r := by linarith
  have hτs : τ < s := WithTop.coe_lt_coe.mp (hτ ▸
    spatialHitTime_lt_of_dist_lt h.1 z r hs0 s (hd.trans_lt her))
  have hl : z ∈ survivingDomain γ τ := survivingDomain_antitone γ hτs.le hs
  have hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 τ) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane hy hw, ?_⟩
    rintro ⟨t, ht, rfl⟩
    have hh := spatialHitTime_lt_of_dist_lt h.1 z r hs0 t (mem_ball.mp hw)
    rw [hτ] at hh
    exact not_lt_of_ge ht.2 (WithTop.coe_lt_coe.mp hh)
  have hb := ball_subset_survivingDomain hr hl hfree
  have hgs := hb (mem_ball.mpr (hd.trans_lt her))
  refine ⟨hτs, hl, hgs, ?_⟩
  rw [dist_sub_right]
  have hbound := source_halfplane_map_local_bound hr hε.le he
    ((h.2.2.2.1 τ).mono hb) (fun w hw => h.2.2.2.2.2.1 τ (hb hw)) hd
  apply hbound.trans_lt
  apply (div_lt_div_iff_of_pos_right hr).mpr
  have hp : 0 < (G τ z).im * ε := mul_pos (h.2.2.2.2.2.1 τ hl) hε
  nlinarith

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsLivePathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance windowBoundsLivePathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma source_liveIndicator_zero_of_coarse_top
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (he : ε < r) (hy : r ≤ z.im) (htop : spatialHitTime γ z r = ⊤) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) = 0 := by
  have hs0 : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hl : liveSpatialHitTime γ z ε = ⊤ := by
    by_contra hn
    obtain ⟨s, _, hd⟩ := (source_liveSpatialHitTime_ne_top_iff γ z ε).mp hn
    have hh := spatialHitTime_lt_of_dist_lt h.1 z r hs0 s (hd.trans_lt he)
    rw [htop] at hh
    exact not_lt_of_ge le_top hh
  simp only [ite_eq_left hl]

lemma source_restarted_kernel_dominates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (τ : ℝ≥0) (hτ : spatialHitTime γ z r = τ)
    (p : C(ℝ≥0, ℂ))
    (hfwd : ∀ t : ℝ≥0, γ (τ + t) ∈ survivingDomain γ τ →
      p t = G τ (γ (τ + t)) - (U τ : ℂ)) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) ≤
      sourceApproachKernel ε r ((if z ∈ survivingDomain γ τ then G τ z else 0) - (U τ : ℂ), p) := by
  by_cases ht : liveSpatialHitTime γ z ε = ⊤
  · simp only [ite_eq_left ht, sourceApproachKernel]
    split_ifs <;> norm_num
  · obtain ⟨s, hs, hd⟩ := (source_liveSpatialHitTime_ne_top_iff γ z ε).mp ht
    obtain ⟨hτs, hl, hgs, hb⟩ := source_live_contact_restarts h z r ε hr hε he hy τ hτ s hs hd
    have heq : τ + (s - τ) = s := add_tsub_cancel_of_le hτs.le
    have hf := hfwd (s - τ) (by simpa only [heq] using hgs)
    simp only [heq] at hf
    have hhit : ∃ t : ℝ≥0, dist (p t) (G τ z - (U τ : ℂ)) <
        8 * (G τ z - (U τ : ℂ)).im * ε / r := by
      refine ⟨s - τ, ?_⟩
      simpa only [hf, Complex.sub_im, Complex.ofReal_im, sub_zero] using hb
    simp only [ite_eq_right ht, ite_eq_left hl, sourceApproachKernel, ite_eq_left hhit, le_refl]

lemma source_stopped_kernel_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    {U' : ℝ≥0 → ℝ} {γ' : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U') (hw' : IsCapacityTwoWitness U' γ' G' F')
    (z : ℂ) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hy : 8 * ε ≤ r) (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (τ : ℝ≥0) (hτ : spatialHitTime γ' z r = τ) :
    (∫ p, sourceApproachKernel ε r
      ((if z ∈ survivingDomain γ' τ then G' τ z else 0) - (U' τ : ℂ), p)
      ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) ≤
      sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ U' γ' G' z r := by
  have ht : spatialHitTime γ' z r ≠ ⊤ := by rw [hτ]; exact WithTop.coe_ne_top
  have he : (spatialHitTime γ' z r).untopD 0 = τ := by rw [hτ]; rfl
  by_cases hz : z ∈ survivingDomain γ' τ
  · have hζ : G' τ z - (U' τ : ℂ) ∈ upperHalfPlane := by
      change 0 < (G' τ z - (U' τ : ℂ)).im
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hw'.imag_positive τ z hz
    have hRb : fullRadius G' τ z ≤ (128 * Real.pi) * r := by
      have hh := hw'.radius_le_past_distance hU τ z hz τ le_rfl
      rwa [dist_comm z, spatialHitTime_mem hw'.1 z r τ hτ] at hh
    have hb := source_kernel_mean_bound hB κ hκ hκ8 γ G F hw hgm
      (G' τ z - (U' τ : ℂ)) hζ ε r (fullRadius G' τ z) hε hr hy hsmall
      (hw'.fullRadius_positive hU τ z hz) hRb
    simpa only [ite_eq_left hz, spatialGreenWeight, ite_eq_right ht, he, greenDensity, ite_eq_left hz] using hb
  · have hk (p : C(ℝ≥0, ℂ)) : sourceApproachKernel ε r ((0:ℂ) - (U' τ : ℂ), p) = 0 :=
      sourceApproachKernel_zero hε.le hr.le (by simp)
    simp only [hk, integral_zero, spatialGreenWeight, ite_eq_right ht, he,
      greenDensity, ite_eq_right hz, mul_zero, le_refl]

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsIntegralPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance windowBoundsIntegralPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance windowBoundsDriverPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance windowBoundsDriverPathBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma source_finite_approach_setIntegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (z : ℂ) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (h8 : 8 * ε ≤ r) (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (σ : a.samples → ℝ≥0)
    (hσ : IsStoppingTime a.filtration (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set a.samples) (hA : MeasurableSet[hσ.measurableSpace] A)
    (hAσ : ∀ ω ∈ A, spatialHitTime (γ ω) z r = (σ ω : WithTop ℝ≥0)) :
    (∫ ω in A, (if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1)
      ∂P.comap Subtype.val) ≤
    ∫ ω in A, sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ∂P.comap Subtype.val := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let gp := sourceTracePath (fun ω : a.samples => γ ω) (fun ω => (a.witness ω).1)
  have hgm : Measurable gp := source_path_measurable gp (fun t =>
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl)
  let ν := μ.map gp
  let : IsProbabilityMeasure ν := inferInstance
  obtain ⟨Φ, hΦm, _, hΦ⟩ := sourceStoppedTraceLaw_forward κ hκ hκ8
    a.B a.brownian a.measurable_B a.continuous_B (fun ω : a.samples => γ ω)
    a.G a.F a.witness
  obtain ⟨hlaw, hfwd⟩ := hΦ σ hσ
  let rp := sourceRestartDriverPath a.B a.continuous_B σ
  let X (ω : a.samples) := Φ (rp ω)
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable a.measurable_B a.continuous_B
      (stopping_time_measurable_nnreal hσ)))
  have hXm : Measurable X := hΦm.comp hrm
  let Y (ω : a.samples) : ℂ :=
    (if z ∈ survivingDomain (γ ω) (σ ω) then a.G ω (σ ω) z else 0) -
      (Real.sqrt κ * a.B (σ ω) ω : ℝ)
  have hYm : Measurable[hσ.measurableSpace] Y := by
    have hGm := measurable_stoppedValue
      (source_killedChart_progressive a.measurable_B a.continuous_B κ
        (fun ω : a.samples => γ ω) a.G a.F a.witness z) hσ
    have hBm := measurable_stoppedValue
      ((Filtration.stronglyAdapted_natural (fun t => (a.measurable_B t).stronglyMeasurable)).isStronglyProgressive_of_continuous a.continuous_B) hσ
    exact hGm.sub (Complex.measurable_ofReal.comp (measurable_const.mul hBm))
  let H (ω : a.samples) := sourceApproachKernel ε r (Y ω, X ω)
  let K (ω : a.samples) := ∫ p, sourceApproachKernel ε r (Y ω, p) ∂ν
  have hHmeas : Measurable H := (sourceApproachKernel_measurable ε r).comp
    ((hYm.mono hσ.measurableSpace_le le_rfl).prodMk hXm)
  have hHi : Integrable H μ :=
    (integrable_const (1:ℝ)).mono' hHmeas.aestronglyMeasurable
      (Eventually.of_forall (fun ω => sourceApproachKernel_norm_le ε r (Y ω, X ω)))
  have hcond : μ[H | hσ.measurableSpace] =ᵐ[μ] K :=
    source_parameter_condExp hσ.measurableSpace_le hXm hYm hlaw
      (sourceApproachKernel ε r) (sourceApproachKernel_measurable ε r)
      (sourceApproachKernel_norm_le ε r)
  have hKi : Integrable K μ := integrable_condExp.congr hcond
  let W (ω : a.samples) := sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r
  have hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hWm : Measurable W := measurable_const.mul
    ((source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z r hτ).mono hτ.measurableSpace_le le_rfl)
  have hWi : Integrable W μ := by
    apply Integrable.of_bound hWm.aestronglyMeasurable
      (sourceApproachConstant κ * ε ^ codimension κ * r ^ (-codimension κ))
    apply Eventually.of_forall
    intro ω
    have hb := (a.witness ω).spatialGreenWeight_bound
      (continuous_const.mul (a.continuous_B ω)) hκ hκ8 hr z hy
    have hc : 0 ≤ sourceApproachConstant κ * ε ^ codimension κ :=
      mul_nonneg (sourceApproachConstant_pos κ hκ hκ8).le (Real.rpow_nonneg hε.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 hc
  have hfi : Integrable (fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (by linarith)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    split_ifs <;> norm_num
  have hAm : MeasurableSet A := hσ.measurableSpace_le A hA
  calc
    _ ≤ ∫ ω in A, H ω ∂μ := by
      apply integral_mono_ae hfi.integrableOn hHi.integrableOn
      filter_upwards [ae_restrict_of_ae hfwd, ae_restrict_mem hAm] with ω hf hωA
      exact source_restarted_kernel_dominates (a.witness ω) z r ε hr hε he hy
        (σ ω) (hAσ ω hωA) (X ω) hf
    _ = ∫ ω in A, K ω ∂μ := by
      have : IsFiniteMeasure (μ.trim hσ.measurableSpace_le) := isFiniteMeasure_trim _
      rw [← integral_congr_ae (ae_restrict_of_ae hcond)]
      exact (setIntegral_condExp hσ.measurableSpace_le hHi hA).symm
    _ ≤ ∫ ω in A, W ω ∂μ := by
      apply integral_mono_ae hKi.integrableOn hWi.integrableOn
      filter_upwards [ae_restrict_mem hAm] with ω hωA
      exact source_stopped_kernel_mean_bound a.brownian κ hκ hκ8
        (fun ω : a.samples => γ ω) a.G a.F a.witness hgm
        (continuous_const.mul (a.continuous_B ω)) (a.witness ω)
        z ε r hε hr h8 hsmall (σ ω) (hAσ ω hωA)

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 
end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
universe u_source_approach
 

def SourceConditionalApproachTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
  ∀ (Ω : Type u_source_approach) (_ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r : ℝ), 0 < ε → ε ≤ q * r → r ≤ z.im →
  ∃ hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    μ[(fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0 : ℝ) else 1)
      | hτ.measurableSpace] ≤ᵐ[μ]
      (fun ω => C * ε ^ codimension κ * spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)

lemma source_approach_small_scale (ε r : ℝ) (hε : 0 < ε)
    (h : ε ≤ min (1/16) (1/(Real.exp 1 * (512 * Real.pi))) * r) :
    0 < r ∧ ε ≤ r/2 ∧ 8*ε ≤ r ∧ Real.exp 1 * (512 * Real.pi) * ε ≤ r := by
  have hA : 0 < Real.exp 1 * (512 * Real.pi) := by positivity
  have hq : 0 < min (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi))) := by positivity
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have h16 : ε ≤ r/16 := by
    apply h.trans
    have hh := mul_le_mul_of_nonneg_right
      (min_le_left (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi)))) hr.le
    nlinarith
  refine ⟨hr, by linarith, by linarith, ?_⟩
  have hqA := (le_div_iff₀ hA).mp
    (min_le_right (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi))))
  have hh := mul_le_mul_of_nonneg_right hqA hr.le
  have hhh := mul_le_mul_of_nonneg_left h hA.le
  nlinarith only [hh, hhh]

 

theorem sourceConditionalApproach_proved : SourceConditionalApproachTarget := by
  intro κ hκ hκ8
  refine ⟨sourceApproachConstant κ, sourceApproachConstant_pos κ hκ hκ8,
    min (1/16) (1/(Real.exp 1 * (512 * Real.pi))), by positivity, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num)
  intro Ω mΩ P hP γ a z ε r hε hεq hy
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  obtain ⟨hr, he, h8, hsmall⟩ := source_approach_small_scale ε r hε hεq
  let τ (ω : a.samples) := spatialHitTime (γ ω) z r
  have hτ : IsStoppingTime a.filtration τ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  refine ⟨hτ, ?_⟩
  let f (ω : a.samples) : ℝ := if liveSpatialHitTime (γ ω) z ε = ⊤ then 0 else 1
  let W (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r
  let g (ω : a.samples) := sourceApproachConstant κ * ε ^ codimension κ * W ω
  have hf : Integrable f μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (by linarith)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp [f]
    split_ifs <;> norm_num
  have hWm : Measurable[hτ.measurableSpace] W :=
    source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z r hτ
  have hgm : Measurable[hτ.measurableSpace] g := measurable_const.mul hWm
  have hg : Integrable g μ := by
    apply Integrable.of_bound (hgm.mono hτ.measurableSpace_le le_rfl).aestronglyMeasurable
      (sourceApproachConstant κ * ε ^ codimension κ * r ^ (-codimension κ))
    apply Eventually.of_forall
    intro ω
    have hb := (a.witness ω).spatialGreenWeight_bound
      (continuous_const.mul (a.continuous_B ω)) hκ hκ8 hr z hy
    have hc : 0 ≤ sourceApproachConstant κ * ε ^ codimension κ :=
      mul_nonneg (sourceApproachConstant_pos κ hκ hκ8).le (Real.rpow_nonneg hε.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 hc
  change μ[f | hτ.measurableSpace] ≤ᵐ[μ] g
  apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hf hg hgm.stronglyMeasurable
  apply source_unbounded_setIntegral_le a.filtration hτ f g hf hg
  · intro ω ht
    constructor
    · exact source_liveIndicator_zero_of_coarse_top (a.witness ω) z r ε (by linarith) hy ht
    · change sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ _ _ _ z r = 0
      change spatialHitTime (γ ω) z r = ⊤ at ht
      simp only [spatialGreenWeight, ite_eq_left ht, mul_zero]
  · intro n A hA hAτ
    exact source_finite_approach_setIntegral_bound hκ hκ8 a z ε r hε hr he hy h8 hsmall
      (sourceStopTruncate τ n) (sourceStopTruncate_stopping a.filtration hτ n) A hA hAτ

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
universe u_source_spatial
 

end
end SLEExactGauge
end
end

end OAI
