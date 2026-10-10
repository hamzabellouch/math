import Mathlib
import OAI.Probability.SLELocalization.Charge
import OAI.Probability.SLELocalization.PhysicalPast
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Finite Tilt estimates. -/

section
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace SLEExactGauge.FiniteTilt

structure CommonCutoff (A : Set ℂ) (u : ℂ → ℝ) where
  angle : ℝ
  angle_pos : 0 < angle
  height : ℝ
  height_pos : 0 < height
  horizon : ℝ≥0
  horizon_pos : 0 < (horizon:ℝ)
  angle_initial : ∀ z ∈ A, angle < z.im/‖z‖
  height_small : ∀ z ∈ A, height < z.im*Real.exp (-u z/(2*angle^2))
  time_large : ∀ z ∈ A, u z*z.im^2/(4*angle^4) < horizon

def CommonCutoff.at {A : Set ℂ} {u : ℂ → ℝ} (C : CommonCutoff A u)
    (z : ℂ) (hz : z ∈ A) : Cutoff z (u z) where
  angle := C.angle
  angle_pos := C.angle_pos
  angle_initial := C.angle_initial z hz
  height := C.height
  height_pos := C.height_pos
  horizon := C.horizon
  horizon_pos := C.horizon_pos
  height_small := C.height_small z hz
  time_large := C.time_large z hz

lemma commonCutoffs {A : Set ℂ} {u : ℂ → ℝ} {H U α : ℝ}
    (hH : 1 ≤ H) (hU : 0 ≤ U) (hα : 0 < α)
    (hy : ∀ z ∈ A, 1 ≤ z.im ∧ z.im ≤ H)
    (hu : ∀ z ∈ A, 0 ≤ u z ∧ u z ≤ U)
    (hs : ∀ z ∈ A, α ≤ z.im/‖z‖) :
    ∃ Cs : ℕ → CommonCutoff A u, Tendsto (fun n => (Cs n).angle) atTop (𝓝 0) := by
  let δ : ℕ → ℝ := fun n => (α/2)/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδα (n : ℕ) : δ n < α := by
    have hh : 1 ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have he := div_le_self (by positivity : 0 ≤ α/2) hh
    exact he.trans_lt (by linarith)
  let ε : ℕ → ℝ := fun n => Real.exp (-U/(2*(δ n)^2))/2
  let T : ℕ → ℝ≥0 := fun n => ⟨U*H^2/(4*(δ n)^4)+1,by positivity⟩
  let Cs : ℕ → CommonCutoff A u := fun n => {
    angle := δ n
    angle_pos := hδ n
    height := ε n
    height_pos := by dsimp [ε]; positivity
    horizon := T n
    horizon_pos := by
      have hn : 0 ≤ U*H^2/(4*(δ n)^4) := by positivity
      change 0 < U*H^2/(4*(δ n)^4)+1
      linarith
    angle_initial := fun z hz => (hδα n).trans_le (hs z hz)
    height_small := by
      intro z hz
      have hu' := (hu z hz).2
      have he : Real.exp (-U/(2*(δ n)^2)) ≤ Real.exp (-u z/(2*(δ n)^2)) := by
        apply Real.exp_le_exp.2
        exact div_le_div_of_nonneg_right (neg_le_neg hu') (by positivity)
      have hz' := (hy z hz).1
      dsimp only [ε]
      have hp := Real.exp_pos (-U/(2*(δ n)^2))
      nlinarith [Real.exp_pos (-u z/(2*(δ n)^2))]
    time_large := by
      intro z hz
      have hz0 : 0 ≤ z.im := (by norm_num : (0:ℝ) ≤ 1).trans (hy z hz).1
      have hz2 : z.im^2 ≤ H^2 := pow_le_pow_left₀ hz0 (hy z hz).2 2
      have hm := mul_le_mul (hu z hz).2 hz2 (sq_nonneg _) hU
      have hd := div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 4*(δ n)^4)
      change u z*z.im^2/(4*(δ n)^4) < U*H^2/(4*(δ n)^4)+1
      linarith }
  refine ⟨Cs,?_⟩
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds (x := α/2) (f := atTop)).div_atTop ht
  simpa only [Cs,δ] using hh

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerCutoff

lemma solution_mark_dist_le {ε T D δ : ℝ} (hε : 0 < ε)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) {U V : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (V t) (G t)) (Icc 0 T) t)
    (h0 : dist (H 0) (G 0) ≤ δ) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ D)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (H t) (G t) ≤ (δ+D)*Real.exp ((4/ε^2)*T) := by
  let K : ℝ≥0 := ⟨4/ε^2,by positivity⟩
  have hK : (0:ℝ) < K := by change 0 < 4/ε^2; positivity
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      dist (velocity ε (V s) (G s)) (velocity ε (U s) (G s)) ≤ (K:ℝ)*D := by
    rw [dist_eq_norm]
    calc
      _ ≤ (4/ε^2)*|V s-U s| := norm_velocity_driver_sub_le hε _ _ _
      _ ≤ (K:ℝ)*D := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hUV s ⟨hs.1,hs.2.le⟩) hK.le
  have hh := dist_le_of_approx_trajectories_ODE
    (fun t => velocity_lipschitz hε (U t))
    (HasDerivWithinAt.continuousOn hH) (fun _ hs => derivWithin_right hH hs)
    (fun t _ => le_of_eq (dist_self (velocity ε (U t) (H t))))
    (HasDerivWithinAt.continuousOn hG) (fun _ hs => derivWithin_right hG hs)
    hb h0 t ht
  have he : gronwallBound δ K (0+(K:ℝ)*D) (t-0) =
      δ*Real.exp ((K:ℝ)*t)+D*(Real.exp ((K:ℝ)*t)-1) := by
    simp only [gronwallBound,zero_add,sub_zero,ite_eq_right (ne_of_gt hK)]
    field_simp
  rw [he] at hh
  have hexp : Real.exp ((K:ℝ)*t) ≤ Real.exp ((K:ℝ)*T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK.le)
  apply hh.trans
  change δ*Real.exp ((K:ℝ)*t)+D*(Real.exp ((K:ℝ)*t)-1) ≤ (δ+D)*Real.exp ((K:ℝ)*T)
  have h1 := mul_le_mul_of_nonneg_left hexp hδ
  have h2 := mul_le_mul_of_nonneg_left hexp hD
  nlinarith

lemma solutionPath_joint_lipschitz {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    LipschitzWith ⟨2*Real.exp ((4/ε^2)*T),by positivity⟩
      (fun p : C(I, ℝ) × ℂ => solutionPath hε hT p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨U,z⟩ ⟨V,w⟩
  apply (ContinuousMap.dist_le (show 0 ≤ (2*Real.exp ((4/ε^2)*T))*dist (U,z) (V,w) by positivity)).2
  intro t
  have hh := solution_mark_dist_le hε (D := dist U V) (δ := dist z w)
    dist_nonneg dist_nonneg (solution_deriv hε hT U z) (solution_deriv hε hT V w)
    (by rw [solution_initial,solution_initial])
    (fun s _ => ContinuousMap.dist_apply_le_dist (f := U) (g := V) (projIcc 0 1 zero_le_one (s/T))) t.property
  apply hh.trans
  change (dist z w+dist U V)*Real.exp ((4/ε^2)*T) ≤
    (2*Real.exp ((4/ε^2)*T))*max (dist U V) (dist z w)
  have hsum : dist z w+dist U V ≤ 2*max (dist U V) (dist z w) := by
    linarith [le_max_left (dist U V) (dist z w),le_max_right (dist U V) (dist z w)]
  nlinarith [mul_le_mul_of_nonneg_right hsum (Real.exp_pos ((4/ε^2)*T)).le]

lemma continuous_mark_position {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Continuous (fun p : (C(I,ℝ) × ℂ) × ℝ => position hε hT p.1.1 p.1.2 p.2) := by
  exact continuous_eval.comp (((solutionPath_joint_lipschitz hε hT).continuous.comp continuous_fst).prodMk
    ((continuous_projIcc (h := hT)).comp continuous_snd))

lemma continuous_mark_variation {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Continuous (fun p : (C(I,ℝ) × ℂ) × ℝ => variation hε hT p.1.1 p.1.2 p.2) := by
  have hd : Continuous (fun p : (C(I,ℝ) × ℂ) × ℝ => extendDriver T p.1.1 p.2) :=
    (continuous_joint_extendDriver T).comp ((continuous_fst.fst).prodMk continuous_snd)
  have hw := (continuous_mark_position hε hT).sub (Complex.continuous_ofReal.comp hd)
  exact Complex.continuous_re.comp (continuous_const.div
    (((continuous_clampIm ε).comp hw).pow 2) (fun _ => pow_ne_zero 2 (clampIm_ne_zero hε _)))

lemma continuous_mark_logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Continuous (fun p : (C(I,ℝ) × ℂ) × ℝ => logDerivative hε hT p.1.1 p.1.2 p.2) := by
  have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := 0) (f := fun p : C(I,ℝ) × ℂ => variation hε hT p.1 p.2)
    (continuous_mark_variation hε hT)
  exact hc.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp ((continuous_projIcc (h := hT)).comp continuous_snd)))

lemma continuous_mark_green {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (p a : ℝ) :
    Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ =>
      LoewnerField.field hε hT p a 1 q.1.1 q.1.2 q.2 (extendDriver T q.1.1 q.2)) := by
  have hH := continuous_mark_position hε hT
  have hD : Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ => extendDriver T q.1.1 q.2) :=
    (continuous_joint_extendDriver T).comp (continuous_fst.fst.prodMk continuous_snd)
  apply GreenPhysical.continuous_green_comp p a
  · exact (Complex.continuous_re.comp hH).sub (continuous_const.mul hD)
  · exact continuous_const.max (Complex.continuous_im.comp hH)
  · exact continuous_mark_logDerivative hε hT
  · intro q
    exact LoewnerField.height_pos hε hT q.1.1 q.1.2 q.2

end SLEExactGauge.LoewnerCutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerCutoff
open LoewnerField LoewnerExit
local instance commonClocksMarkRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance commonClocksMarkRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩

lemma continuous_mark_field {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (p a sdev : ℝ) :
    Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ =>
      field hε hT p a sdev q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hH := (continuous_mark_position hε hT).comp
    (continuous_fst : Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ => q.1))
  apply GreenPhysical.continuous_green_comp p a
  · exact (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd)
  · exact continuous_const.max (Complex.continuous_im.comp hH)
  · exact (continuous_mark_logDerivative hε hT).comp continuous_fst
  · intro q
    exact height_pos hε hT q.1.1.1 q.1.1.2 q.1.2

lemma continuous_mark_first {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (p a sdev : ℝ) :
    Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ =>
      iteratedDeriv 1 (field hε hT p a sdev q.1.1.1 q.1.1.2 q.1.2) q.2) := by
  simp only [first_eq]
  have hH := (continuous_mark_position hε hT).comp
    (continuous_fst : Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ => sdev*q.2))
  have hy : Continuous (fun q : ((C(I,ℝ) × ℂ) × ℝ) × ℝ => height hε hT q.1.1.1 q.1.1.2 q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  exact ((continuous_const.mul hx).div ((hx.pow 2).add (hy.pow 2))
    (fun q => (GreenPhysical.q_pos _ (height_pos hε hT q.1.1.1 q.1.1.2 q.1.2)).ne')).mul
      (continuous_mark_field hε hT p a sdev)

lemma continuous_mark_deficit {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ : ℝ) :
    Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ => deficit hε hT q.1.1 q.1.2 ρ δ q.2) := by
  have hH := continuous_mark_position hε hT
  have hD : Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ => extendDriver T q.1.1 q.2) :=
    (continuous_joint_extendDriver T).comp (continuous_fst.fst.prodMk continuous_snd)
  have hr : Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ => radius hε hT q.1.1 q.1.2 q.2) :=
    (continuous_const.mul (Complex.continuous_im.comp hH)).div
      (Real.continuous_exp.comp (continuous_mark_logDerivative hε hT)) (fun _ => Real.exp_ne_zero _)
  have hs : Continuous (fun q : (C(I,ℝ) × ℂ) × ℝ => sine hε hT q.1.1 q.1.2 q.2) :=
    (Complex.continuous_im.comp hH).div
      (((continuous_clampIm ε).comp (hH.sub (Complex.continuous_ofReal.comp hD))).norm)
      (fun _ => norm_ne_zero_iff.2 (clampIm_ne_zero hε _))
  exact (hr.sub continuous_const).min
    (((Complex.continuous_im.comp hH).sub continuous_const).min (hs.sub continuous_const))

lemma continuous_mark_exitPath {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ : ℝ) :
    Continuous (fun q : C(I,ℝ) × ℂ => exitPath hε hT q.1 q.2 ρ δ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry _
  exact (continuous_mark_deficit hε hT ρ δ).comp
    (continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))

lemma measurable_mark_stop {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ : ℝ) :
    Measurable (fun q : C(I,ℝ) × ℂ => stop hε hT q.1 q.2 ρ δ) :=
  measurable_const.mul (ContinuousExit.measurable_time.comp (continuous_mark_exitPath hε hT ρ δ).measurable)

lemma isOpen_mark_positive_on {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ t : ℝ) :
    IsOpen {q : C(I,ℝ) × ℂ | ∀ s ∈ Icc 0 t, 0 < deficit hε hT q.1 q.2 ρ δ s} := by
  let S : Set ((C(I,ℝ) × ℂ) × Icc 0 t) := {q | deficit hε hT q.1.1 q.1.2 ρ δ q.2 ≤ 0}
  have hc : IsClosed S := isClosed_le ((continuous_mark_deficit hε hT ρ δ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) continuous_const
  have hh := isClosedMap_fst_of_compactSpace S hc
  have he : {q : C(I,ℝ) × ℂ | ∀ s ∈ Icc 0 t, 0 < deficit hε hT q.1 q.2 ρ δ s} = (Prod.fst '' S)ᶜ := by
    ext q
    simp only [mem_ofPred_eq,mem_compl_iff,mem_image,S,not_exists,not_and]
    constructor
    · intro hp v hv hvq
      subst q
      exact (not_lt_of_ge hv) (hp v.2 v.2.property)
    · intro hp s hs
      by_contra hn
      exact hp (q,⟨s,hs⟩) (not_lt.1 hn) rfl
  rw [he]
  exact hh.isOpen_compl

lemma measurable_mark_coeffAt {ε : ℝ} (hε : 0 < ε) (s : ℝ≥0) (p a sdev ρ δ : ℝ) :
    Measurable (fun q : (C(I,ℝ) × ℝ) × ℂ =>
      LoewnerLocalized.coeffAt hε 1 s p a sdev q.2 ρ δ q.1) := by
  have hp : Continuous (fun q : (C(I,ℝ) × ℝ) × ℂ => (((q.1.1,q.2),(s:ℝ)),q.1.2)) :=
    ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_const).prodMk continuous_fst.snd
  have hc := (continuous_mark_first hε s.coe_nonneg p a sdev).comp hp
  dsimp only [Function.comp_def] at hc
  exact hc.measurable.ite (((isOpen_mark_positive_on hε s.coe_nonneg ρ δ s).preimage
    (continuous_fst.fst.prodMk continuous_snd)).measurableSet) measurable_const

end SLEExactGauge.LoewnerCutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.PhysicalPast

lemma joint_avoids_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (T : ℝ≥0) :
    @MeasurableSet (Ω × ℂ) (Prod.instMeasurableSpace (α := Ω) (β := ℂ)
      (m₁ := BrownianPredictable.pastSigma B T) (m₂ := inferInstance))
      {q | q.1 ∈ avoids κ B q.2 ε T} := by
  let : MeasurableSpace Ω := BrownianPredictable.pastSigma B T
  change MeasurableSet {q : Ω × ℂ | ∃ m : ℕ, ∀ n : ℕ, ε + CanonicalTrace.height m ≤
    dist q.2 (CanonicalTrace.value κ B (sampleTime T (TopologicalSpace.denseSeq I n)) q.1)}
  simp only [ofPred_exists,ofPred_forall]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le measurable_const (measurable_snd.dist
    (((CanonicalTrace.measurable_past κ B _).mono
      (BrownianPredictable.pastSigma_mono B (sampleTime_le T (TopologicalSpace.denseSeq I n))) le_rfl).comp measurable_fst))

end SLEExactGauge.PhysicalPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerLocalized
open BrownianPredictable
local instance commonClocksPastRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance commonClocksPastRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩

lemma joint_rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    {ε : ℝ} (hε : 0 < ε) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0) (p a sdev ρ δ : ℝ) :
    @Measurable (Ω × ℂ) ℝ (Prod.instMeasurableSpace (α := Ω) (β := ℂ)
      (m₁ := pastSigma B s) (m₂ := inferInstance)) _
      (fun q => rawCoeff hε 1 B T s p a sdev q.2 ρ δ q.1) := by
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · have hp : Measurable (fun q : Ω × ℂ =>
        ((BrownianDriver.path B sdev s q.1,B s q.1),q.2)) :=
      (((BrownianDriver.path_measurable_past B sdev s).comp measurable_fst).prodMk
        ((past_measurable_eval B (s := s) le_rfl).comp measurable_fst)).prodMk measurable_snd
    have hh := (LoewnerCutoff.measurable_mark_coeffAt hε s p a sdev ρ δ).comp hp
    dsimp only [Function.comp_def] at hh
    exact hh
  · exact measurable_const

end SLEExactGauge.LoewnerLocalized

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.PhysicalPast

lemma joint_avoids_nullMeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (ν : Measure ℂ) [SFinite ν] (κ ε : ℝ) (T : ℝ≥0) :
    NullMeasurableSet {q : Ω × ℂ | q.1 ∈ avoids κ B q.2 ε T} (P.prod ν) := by
  change NullMeasurableSet {q : Ω × ℂ | ∃ m : ℕ, ∀ n : ℕ, ε + CanonicalTrace.height m ≤
    dist q.2 (CanonicalTrace.value κ B (sampleTime T (TopologicalSpace.denseSeq I n)) q.1)} (P.prod ν)
  simp only [ofPred_exists,ofPred_forall]
  apply NullMeasurableSet.iUnion
  intro m
  apply NullMeasurableSet.iInter
  intro n
  exact nullMeasurableSet_le aemeasurable_const
    (measurable_snd.aemeasurable.dist ((CanonicalTrace.aemeasurable κ hB _).comp_fst))

end SLEExactGauge.PhysicalPast

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerLocalized
local instance commonClocksJointRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance commonClocksJointRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩

lemma joint_rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (ν : Measure ℂ) [SFinite ν] {ε : ℝ} (hε : 0 < ε)
    (T s : ℝ≥0) (p a sdev ρ δ : ℝ) :
    AEMeasurable (fun q : Ω × ℂ => rawCoeff hε 1 B T s p a sdev q.2 ρ δ q.1) (P.prod ν) := by
  unfold rawCoeff
  split_ifs
  · have hp : AEMeasurable (fun q : Ω × ℂ =>
        ((BrownianDriver.path B sdev s q.1,B s q.1),q.2)) (P.prod ν) :=
      (((BrownianDriver.path_aemeasurable hB sdev s).comp_fst).prodMk
        ((hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable.comp_fst)).prodMk measurable_snd.aemeasurable
    have hh := (LoewnerCutoff.measurable_mark_coeffAt hε s p a sdev ρ δ).comp_aemeasurable hp
    dsimp only [Function.comp_def] at hh
    exact hh
  · exact aemeasurable_const

end SLEExactGauge.LoewnerLocalized

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerLocalized BrownianPredictable

def coeff {Ω : Type*} {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T s : ℝ≥0) (ρ δ e : ℝ) (q : Ω × ℂ) : ℝ :=
  if q.1 ∈ PhysicalPast.avoids κ B q.2 e s then
    rawCoeff hε 1 B T s (1-κ/8) (8/κ-1) (Real.sqrt κ) q.2 ρ δ q.1 else 0

lemma coeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0) (ρ δ e : ℝ) :
    @Measurable (Ω × ℂ) ℝ (Prod.instMeasurableSpace (m₁ := pastSigma B s) (m₂ := inferInstance)) _
      (coeff hε κ B T s ρ δ e) := by
  exact (joint_rawCoeff_measurable_past hε B T s _ _ _ ρ δ).ite
    (PhysicalPast.joint_avoids_measurable_past κ B e s) measurable_const

lemma coeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (ν : Measure ℂ) [SFinite ν] {ε : ℝ} (hε : 0 < ε)
    (κ : ℝ) (T s : ℝ≥0) (ρ δ e : ℝ) :
    AEMeasurable (coeff hε κ B T s ρ δ e) (P.prod ν) := by
  exact (joint_rawCoeff_aemeasurable hB ν hε T s _ _ _ ρ δ).indicator₀
    (PhysicalPast.joint_avoids_nullMeasurable hB ν κ e s)

lemma coeff_uniform_bound {Ω : Type*} {ε : ℝ} (hε : 0 < ε)
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ρ δ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ e s q, |coeff hε κ B T s ρ δ e q| ≤ K := by
  let p := 1-κ/8
  let a := 8/κ-1
  have hp : 0 ≤ p := by dsimp [p]; linarith [hκ.2]
  have ha : 0 ≤ a := by dsimp [a]; have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by linarith [hκ.2]); linarith
  let K := max 0 (|Real.sqrt κ| *((2*ε/Real.exp ((2/ε^2)*T))^(-p)*a/ε))
  refine ⟨K,le_max_left _ _,?_⟩
  intro e s q
  unfold coeff rawCoeff coeffAt
  split_ifs with h1 h2 h3
  · have hh := first_bound hε s.coe_nonneg p a (Real.sqrt κ) hp ha
      (BrownianDriver.path B (Real.sqrt κ) s q.1) q.2 s (B s q.1)
    apply hh.trans
    have hs : (s:ℝ) ≤ T := h2.le
    have he : Real.exp ((2/ε^2)*s) ≤ Real.exp ((2/ε^2)*T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs (by positivity))
    have hb : (2*ε/Real.exp ((2/ε^2)*T)) ≤ (2*ε/Real.exp ((2/ε^2)*s)) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) he
    have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2*ε/Real.exp ((2/ε^2)*T)) hb (neg_nonpos.2 hp)
    apply le_trans _ (le_max_right _ _)
    gcongr
  all_goals simpa only [abs_zero] using (le_max_left 0 (|Real.sqrt κ| *((2*ε/Real.exp ((2/ε^2)*T))^(-p)*a/ε)))

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.CompactHit
local instance commonClocksHitComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance commonClocksHitComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def hits (e : ℝ) (p : C(I,ℂ) × ℂ) : Prop := ∃ q : I, dist p.2 (p.1 q) ≤ e

def time (e : ℝ) (p : C(I,ℂ) × ℂ) : I := sInf {q : I | dist p.2 (p.1 q) ≤ e}

lemma hits_closed (e : ℝ) : IsClosed {p : C(I,ℂ) × ℂ | hits e p} := by
  have hc : IsClosed {q : (C(I,ℂ) × ℂ) × I | dist q.1.2 (q.1.1 q.2) ≤ e} :=
    isClosed_le (continuous_fst.snd.dist (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))) continuous_const
  have he : {p : C(I,ℂ) × ℂ | hits e p} = Prod.fst ''
      {q : (C(I,ℂ) × ℂ) × I | dist q.1.2 (q.1.1 q.2) ≤ e} := by
    ext p
    simp [hits]
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

lemma time_mem {e : ℝ} {p : C(I,ℂ) × ℂ} (hp : hits e p) :
    dist p.2 (p.1 (time e p)) ≤ e := by
  exact (isClosed_le (continuous_const.dist p.1.continuous) continuous_const).isCompact.sInf_mem hp

lemma time_le {e : ℝ} {p : C(I,ℂ) × ℂ} {q : I} (hq : dist p.2 (p.1 q) ≤ e) :
    time e p ≤ q := sInf_le hq

lemma before {e : ℝ} {p : C(I,ℂ) × ℂ} {q : I} (hq : q < time e p) :
    e < dist p.2 (p.1 q) := by
  by_contra hm
  exact not_le_of_gt hq (time_le (not_lt.1 hm))

lemma time_eq_one_of_not_hits {e : ℝ} {p : C(I,ℂ) × ℂ} (hp : ¬ hits e p) : time e p = 1 := by
  have he : {q : I | dist p.2 (p.1 q) ≤ e} = ∅ := by
    ext q
    simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
    exact fun hq => hp ⟨q,hq⟩
  simp only [time,he,sInf_empty]
  rfl

lemma time_le_iff {e : ℝ} {p : C(I,ℂ) × ℂ} {q : I} (hq : q < 1) :
    time e p ≤ q ↔ ∃ r : I, r ≤ q ∧ dist p.2 (p.1 r) ≤ e := by
  constructor
  · intro ht
    have hp : hits e p := by
      by_contra hn
      rw [time_eq_one_of_not_hits hn] at ht
      exact not_le_of_gt hq ht
    exact ⟨time e p,ht,time_mem hp⟩
  · rintro ⟨r,hr,hmem⟩
    exact (time_le hmem).trans hr

lemma measurable_time (e : ℝ) : Measurable (time e) := by
  apply measurable_of_Iic
  intro q
  by_cases hq : q = 1
  · have he : time e ⁻¹' Iic q = univ := by
      subst q
      ext p
      simp only [mem_preimage,mem_Iic,mem_univ,iff_true]
      exact (time e p).property.2
    rw [he]
    exact MeasurableSet.univ
  · have hq1 : q < 1 := lt_of_le_of_ne q.property.2 hq
    have hc : IsClosed {r : (C(I,ℂ) × ℂ) × I | r.2 ≤ q ∧ dist r.1.2 (r.1.1 r.2) ≤ e} :=
      (isClosed_le continuous_snd continuous_const).inter
        (isClosed_le (continuous_fst.snd.dist (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))) continuous_const)
    have he : time e ⁻¹' Iic q = Prod.fst ''
        {r : (C(I,ℂ) × ℂ) × I | r.2 ≤ q ∧ dist r.1.2 (r.1.1 r.2) ≤ e} := by
      ext p
      change (time e p ≤ q) ↔ ∃ r, r ∈ {r : (C(I,ℂ) × ℂ) × I | r.2 ≤ q ∧ dist r.1.2 (r.1.1 r.2) ≤ e} ∧ r.1 = p
      rw [time_le_iff hq1]
      constructor
      · rintro ⟨r,hr,hd⟩
        exact ⟨(p,r),⟨hr,hd⟩,rfl⟩
      · rintro ⟨⟨p',r⟩,⟨hr,hd⟩,he⟩
        change p' = p at he
        subst p'
        exact ⟨r,hr,hd⟩
    rw [he]
    exact (isClosedMap_fst_of_compactSpace _ hc).measurableSet

end SLEExactGauge.CompactHit

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.CompactHit

def realTime (T e : ℝ) (V : C(I,ℂ)) (z : ℂ) : ℝ := T*time e (V,z)

lemma realTime_bounds {T : ℝ} (hT : 0 ≤ T) (e : ℝ) (V : C(I,ℂ)) (z : ℂ) :
    realTime T e V z ∈ Icc 0 T :=
  ⟨mul_nonneg hT (time e (V,z)).property.1,by
    simpa only [realTime,mul_one] using mul_le_mul_of_nonneg_left (time e (V,z)).property.2 hT⟩

lemma realTime_le {T e : ℝ} (hT : 0 < T) (V : C(I,ℂ)) (γ : ℝ → ℂ) (z : ℂ)
    (hV : ∀ q : I, V q = γ (T*q)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hd : dist z (γ t) ≤ e) : realTime T e V z ≤ t := by
  let q : I := ⟨t/T,⟨div_nonneg ht.1 hT.le,(div_le_one hT).2 ht.2⟩⟩
  have he : T*(q:ℝ) = t := mul_div_cancel₀ _ hT.ne'
  have hq : dist z (V q) ≤ e := by rw [hV,he]; exact hd
  have hm : (time e (V,z):ℝ) ≤ (q:ℝ) := time_le hq
  have hx := mul_le_mul_of_nonneg_left hm hT.le
  rwa [he] at hx

lemma realTime_hits {T e : ℝ} (hT : 0 < T) (V : C(I,ℂ)) (γ : ℝ → ℂ) (z : ℂ)
    (hV : ∀ q : I, V q = γ (T*q)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hd : dist z (γ t) ≤ e) : hits e (V,z) := by
  let q : I := ⟨t/T,⟨div_nonneg ht.1 hT.le,(div_le_one hT).2 ht.2⟩⟩
  refine ⟨q,?_⟩
  change dist z (V q) ≤ e
  rw [hV,mul_div_cancel₀ _ hT.ne']
  exact hd

lemma realTime_stop {T e : ℝ} (hT : 0 < T) (V : C(I,ℂ)) (γ : ℝ → ℂ) (z : ℂ)
    (hV : ∀ q : I, V q = γ (T*q)) (hh : hits e (V,z))
    (hl : z ∈ localizationDomain γ (realTime T e V z)) :
    firstLiveDistanceStop γ z e = ENNReal.ofReal (realTime T e V z) := by
  have hb := realTime_bounds hT.le e V z
  have hd : dist z (γ (realTime T e V z)) ≤ e := by
    simpa only [hV,realTime] using time_mem hh
  let t₀ : ℝ≥0 := ⟨realTime T e V z,hb.1⟩
  have hle : firstLiveDistanceStop γ z e ≤ (t₀ : ℝ≥0∞) := PhysicalStop.le_of_hit hl hd
  have hc : (t₀ : ℝ≥0∞) = ENNReal.ofReal (realTime T e V z) :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hc] at hle
  apply le_antisymm hle
  apply le_sInf
  rintro r ⟨s,⟨hsl,hsd⟩,rfl⟩
  have ht : realTime T e V z ≤ s := by
    by_cases hsT : (s:ℝ) ≤ T
    · exact realTime_le hT V γ z hV ⟨s.coe_nonneg,hsT⟩ hsd
    · exact hb.2.trans (not_le.1 hsT).le
  exact (ENNReal.ofReal_le_ofReal ht).trans_eq (ENNReal.ofReal_coe_nnreal (p := s))

lemma live_byTime_iff {T e : ℝ} (hT : 0 < T) (V : C(I,ℂ)) (γ : ℝ → ℂ) (z : ℂ)
    (hc : ContinuousOn γ (Ici 0)) (hV : ∀ q : I, V q = γ (T*q)) :
    firstLiveDistanceStop γ z e ≤ ENNReal.ofReal T ↔
      hits e (V,z) ∧ z ∈ localizationDomain γ (realTime T e V z) := by
  constructor
  · intro hh
    obtain ⟨t,he,hl,hd,hmin⟩ := PhysicalStop.finite_spec hc
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh)
    have ht : (t:ℝ) ≤ T := by
      rw [he,← ENNReal.ofReal_coe_nnreal (p := t)] at hh
      exact (ENNReal.ofReal_le_ofReal_iff hT.le).1 hh
    exact ⟨realTime_hits hT V γ z hV ⟨t.coe_nonneg,ht⟩ hd,
      survivingDomain_mono (realTime_le hT V γ z hV ⟨t.coe_nonneg,ht⟩ hd) hl⟩
  · rintro ⟨hh,hl⟩
    rw [realTime_stop hT V γ z hV hh hl]
    exact ENNReal.ofReal_le_ofReal (realTime_bounds hT.le e V z).2

lemma cap_eq_realTime {T e τ : ℝ} (hT : 0 < T) (hτ : τ ∈ Icc 0 T)
    (V : C(I,ℂ)) (γ : ℝ → ℂ) (z : ℂ) (hγ : ContinuousOn γ (Ici 0))
    (hV : ∀ q : I, V q = γ (T*q)) (hl : z ∈ localizationDomain γ τ) :
    PhysicalStop.cap (firstLiveDistanceStop γ z e) τ = min (realTime T e V z) τ := by
  let r := realTime T e V z
  have hr := realTime_bounds hT.le e V z
  have hsmall (hrt : r < τ) : firstLiveDistanceStop γ z e = ENNReal.ofReal r := by
    have hh : hits e (V,z) := by
      by_contra hn
      have he : r = T := by simp only [r,realTime,time_eq_one_of_not_hits hn]; simp
      linarith [hτ.2]
    exact realTime_stop hT V γ z hV hh (survivingDomain_mono hrt.le hl)
  by_cases hfin : firstLiveDistanceStop γ z e = ⊤
  · rw [PhysicalStop.cap,ite_eq_left hfin]
    apply (min_eq_right _).symm
    by_contra hn
    have he := hsmall (lt_of_not_ge hn)
    rw [hfin] at he
    exact ENNReal.ofReal_ne_top he.symm
  · obtain ⟨s,hs,hsl,hsd,hmin⟩ := PhysicalStop.finite_spec hγ hfin
    rw [PhysicalStop.cap,ite_eq_right hfin,hs,ENNReal.coe_toReal]
    apply le_antisymm
    · apply le_min _ (min_le_right _ _)
      by_cases hrt : r < τ
      · have he := hsmall hrt
        rw [hs,← ENNReal.ofReal_coe_nnreal (p := s)] at he
        have hsre : (s:ℝ) = r := (ENNReal.ofReal_eq_ofReal_iff s.coe_nonneg (show 0 ≤ r from hr.1)).1 he
        rw [hsre]
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (not_lt.1 hrt)
    · apply le_min _ (min_le_right _ _)
      by_cases hsT : (s:ℝ) ≤ T
      · exact (min_le_left _ _).trans (realTime_le hT V γ z hV ⟨s.coe_nonneg,hsT⟩ hsd)
      · exact (min_le_right _ _).trans (hτ.2.trans (not_le.1 hsT).le)

lemma realTime_antitone (T : ℝ) (hT : 0 ≤ T) (V : C(I,ℂ)) (z : ℂ) {e e' : ℝ} (he : e ≤ e') :
    realTime T e' V z ≤ realTime T e V z := by
  apply mul_le_mul_of_nonneg_left _ hT
  by_cases hh : hits e (V,z)
  · exact time_le ((time_mem hh).trans he)
  · rw [time_eq_one_of_not_hits hh]
    exact (time e' (V,z)).property.2

end SLEExactGauge.CompactHit

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized
local instance commonClocksObservedRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance commonClocksObservedRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance commonClocksObservedComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance commonClocksObservedComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def observedTime {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ e : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) : ℝ :=
  min (CompactHit.realTime T e q.1.2 q.2) (stop hε hT q.1.1 q.2 ρ δ)

lemma measurable_observedTime {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ e : ℝ) :
    Measurable (observedTime hε hT ρ δ e) := by
  have hv : Measurable (fun q : (C(I,ℝ) × C(I,ℂ)) × ℂ => (q.1.2,q.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hv' := (measurable_subtype_coe.comp ((CompactHit.measurable_time e).comp hv)).const_mul T
  have hu : Measurable (fun q : (C(I,ℝ) × C(I,ℂ)) × ℂ => (q.1.1,q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hs := (measurable_mark_stop hε hT ρ δ).comp hu
  have hh := hv'.min hs
  exact hh

def observedValue {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ e p a : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) : ℝ :=
  let t := observedTime hε hT ρ δ e q
  field hε hT p a 1 q.1.1 q.2 t (extendDriver T q.1.1 t)

lemma measurable_observedValue {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ e p a : ℝ) :
    Measurable (observedValue hε hT ρ δ e p a) := by
  have ht := measurable_observedTime hε hT ρ δ e
  have hx : Measurable (fun q : (C(I,ℝ) × C(I,ℂ)) × ℂ =>
      (((q.1.1,q.2),observedTime hε hT ρ δ e q),extendDriver T q.1.1 (observedTime hε hT ρ δ e q))) :=
    ((measurable_fst.fst.prodMk measurable_snd).prodMk ht).prodMk
      ((continuous_joint_extendDriver T).measurable.comp (measurable_fst.fst.prodMk ht))
  have hh := (continuous_mark_field hε hT p a 1).measurable.comp hx
  exact hh

lemma coeff_common {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (z : ℂ) (hz : z ∈ A) {ρ : ℝ} (hr : (2*z.im)*Real.exp (-u z) = ρ) (e : ℝ) (s : ℝ≥0) (ω : Ω) :
    (C.at z hz).physicalCoeff 1 κ B e s ω =
      coeff C.height_pos κ B C.horizon s ρ C.angle e (ω,z) := by
  simp only [FiniteTilt.Cutoff.physicalCoeff,FiniteTilt.CommonCutoff.at,coeff,hr]

lemma observedValue_eq {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (z : ℂ) (hz : z ∈ A) (hhalf : z ∈ halfPlane) (hu : 0 < u z)
    {ρ : ℝ} (hr : (2*z.im)*Real.exp (-u z) = ρ)
    (V : C(I,ℂ)) (hV : ∀ q : I, V q = γ ω ((C.horizon:ℝ)*q)) (e : ℝ) :
    observedValue C.height_pos C.horizon.coe_nonneg ρ C.angle e (1-κ/8) (8/κ-1)
      ((BrownianDriver.path B (Real.sqrt κ) C.horizon ω,V),z) =
        (C.at z hz).physicalValue κ B γ e ω := by
  let Cz := C.at z hz
  have hs := Cz.source_live κ B ω hm hhalf hu hc hb0
  have hb := Cz.bounds κ B ω
  have ht := CompactHit.cap_eq_realTime (e := e) C.horizon_pos hb V (γ ω) z hm.1 hV hs
  have he : observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle e
      ((BrownianDriver.path B (Real.sqrt κ) C.horizon ω,V),z) = Cz.physicalTime κ B γ e ω := by
    rw [FiniteTilt.Cutoff.physicalTime,ht]
    simp only [observedTime,FiniteTilt.Cutoff.stopTime,FiniteTilt.Cutoff.paths,Cz,FiniteTilt.CommonCutoff.at,hr]
  have hb' := Cz.physicalTime_bounds κ B γ e ω
  have hU := Cz.path_eq κ B ω hc ⟨hb'.1,hb'.2.trans hb.2⟩
  dsimp only [observedValue]
  rw [he]
  change field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) 1 _ z _ _ =
    field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) _ z _ _
  dsimp only [field]
  rw [one_mul]
  change extendDriver (C.horizon:ℝ) (BrownianDriver.path B (Real.sqrt κ) C.horizon ω)
    (Cz.physicalTime κ B γ e ω) = _ at hU
  rw [hU]
  rfl

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Mesh
open TaylorMeshes

def slab (D : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  (if t < b then D t else 0) - (if t < a then D t else 0)

lemma prestop_product (D E : ℝ → ℝ) (a b t : ℝ) :
    (if t < a then D t else 0)*(if t < b then E t else 0) =
      (if t < min a b then D t*E t else 0) := by
  simp only [lt_min_iff]
  split_ifs <;> simp_all

lemma slab_product (D E : ℝ → ℝ) (a b c d t : ℝ) :
    slab D a b t * slab E c d t =
      (if t < min b d then D t*E t else 0) -
      (if t < min b c then D t*E t else 0) -
      (if t < min a d then D t*E t else 0) +
      (if t < min a c then D t*E t else 0) := by
  unfold slab
  rw [sub_mul,mul_sub,mul_sub]
  simp only [prestop_product]
  ring

lemma slab_riemann_tendsto {T a b c d : ℝ} (hT : 0 ≤ T)
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
    (hc : c ∈ Icc 0 T) (hd : d ∈ Icc 0 T)
    {D E : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (slab D a b (mesh T n i)*slab E c d (mesh T n i))*(T/(2:ℝ)^n))
      atTop (𝓝 ((∫ t in 0..min b d, D t*E t) - (∫ t in 0..min b c, D t*E t) -
        (∫ t in 0..min a d, D t*E t) + (∫ t in 0..min a c, D t*E t))) := by
  have hDE : ContinuousOn (fun t => D t*E t) (Icc 0 T) := hD.mul hE
  have hlim (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :=
    StoppedMeshes.prestop_riemann_tendsto hT (le_min hs.1 ht.1)
      ((min_le_left s t).trans hs.2) (hDE.mono (Icc_subset_Icc_right ((min_le_left s t).trans hs.2)))
  have hh := ((hlim b d hb hd).sub (hlim b c hb hc)).sub (hlim a d ha hd) |>.add (hlim a c ha hc)
  convert hh using 1
  funext n
  simp [slab_product,sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,ite_mul]

lemma integral_prestop {T a : ℝ} (ha : a ∈ Icc 0 T) (D : ℝ → ℝ) :
    (∫ t in (0:ℝ)..T, if t < a then D t else 0) = ∫ t in (0:ℝ)..a, D t := by
  calc
    _ = ∫ t in (0:ℝ)..T, Set.indicator {t : ℝ | t ≤ a} D t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ a from by rw [ae_iff]; simp] with t ht htI
      simp only [Set.indicator_apply,mem_ofPred_eq]
      congr 1
      exact propext (lt_iff_le_and_ne.trans (and_iff_left ht))
    _ = _ := intervalIntegral.integral_indicator ha

lemma prestop_intervalIntegrable {T a : ℝ} (hT : 0 ≤ T)
    {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 T)) :
    IntervalIntegrable (fun t => if t < a then D t else 0) volume 0 T := by
  have hh : IntegrableOn D (Ioc 0 T) volume :=
    (hD.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact hh.indicator measurableSet_Iio

lemma slab_product_integral {T a b c d : ℝ} (hT : 0 ≤ T)
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
    (hc : c ∈ Icc 0 T) (hd : d ∈ Icc 0 T)
    {D E : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T)) :
    (∫ t in (0:ℝ)..T, slab D a b t*slab E c d t) =
      (∫ t in 0..min b d, D t*E t) - (∫ t in 0..min b c, D t*E t) -
      (∫ t in 0..min a d, D t*E t) + (∫ t in 0..min a c, D t*E t) := by
  simp_rw [slab_product]
  have hDE : ContinuousOn (fun t => D t*E t) (Icc 0 T) := hD.mul hE
  have hi (s : ℝ) := prestop_intervalIntegrable (a := s) hT hDE
  rw [intervalIntegral.integral_add ((hi _ |>.sub (hi _)).sub (hi _)) (hi _),
    intervalIntegral.integral_sub (hi _ |>.sub (hi _)) (hi _),
    intervalIntegral.integral_sub (hi _) (hi _)]
  rw [integral_prestop ⟨le_min hb.1 hd.1,(min_le_left _ _).trans hb.2⟩,
    integral_prestop ⟨le_min hb.1 hc.1,(min_le_left _ _).trans hb.2⟩,
    integral_prestop ⟨le_min ha.1 hd.1,(min_le_left _ _).trans ha.2⟩,
    integral_prestop ⟨le_min ha.1 hc.1,(min_le_left _ _).trans ha.2⟩]

lemma slab_riemann_tendsto_integral {T a b c d : ℝ} (hT : 0 ≤ T)
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
    (hc : c ∈ Icc 0 T) (hd : d ∈ Icc 0 T)
    {D E : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (slab D a b (mesh T n i)*slab E c d (mesh T n i))*(T/(2:ℝ)^n))
      atTop (𝓝 (∫ t in (0:ℝ)..T, slab D a b t*slab E c d t)) := by
  rw [slab_product_integral hT ha hb hc hd hD hE]
  exact slab_riemann_tendsto hT ha hb hc hd hD hE

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge.Mesh

lemma slab_eq_zero_of_not_mem {D : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b) (ht : t ∉ Icc a b) :
    slab D a b t = 0 := by
  unfold slab
  by_cases hta : t < a
  · simp [hta,hta.trans_le hab]
  · have htb : ¬t < b := by intro h; exact ht ⟨not_lt.1 hta,h.le⟩
    simp [hta,htb]

lemma slab_abs_le {D : ℝ → ℝ} {a b t M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) (h : |D t| ≤ M) :
    |slab D a b t| ≤ M := by
  unfold slab
  by_cases hta : t < a
  · simpa [hta,hta.trans_le hab] using hM
  · by_cases htb : t < b
    · simpa [hta,htb] using h
    · simpa [hta,htb] using hM

lemma measurable_slab {Z : Type*} [MeasurableSpace Z] {D : Z → ℝ → ℝ} {a b : Z → ℝ}
    (hD : Measurable (fun q : ℝ × Z => D q.2 q.1)) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun q : ℝ × Z => slab (D q.2) (a q.2) (b q.2) q.1) := by
  exact (hD.ite (measurableSet_lt measurable_fst (hb.comp measurable_snd)) measurable_const).sub
    (hD.ite (measurableSet_lt measurable_fst (ha.comp measurable_snd)) measurable_const)

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit
local instance commonClocksBoundsRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance commonClocksBoundsRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance commonClocksBoundsComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance commonClocksBoundsComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

lemma observedTime_bounds {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ e : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) : observedTime hε hT ρ δ e q ∈ Icc 0 T := by
  have hr := CompactHit.realTime_bounds hT e q.1.2 q.2
  have hs := stop_bounds hε hT q.1.1 q.2 ρ δ
  exact ⟨le_min hr.1 hs.1,(min_le_left _ _).trans hr.2⟩

lemma observedTime_antitone {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ρ δ : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) {e r : ℝ} (her : e ≤ r) :
    observedTime hε hT ρ δ r q ≤ observedTime hε hT ρ δ e q :=
  min_le_min_right _ (CompactHit.realTime_antitone T hT q.1.2 q.2 her)

lemma observedTime_eq {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (z : ℂ) (hz : z ∈ A) (hhalf : z ∈ halfPlane) (hu : 0 < u z)
    {ρ : ℝ} (hr : (2*z.im)*Real.exp (-u z) = ρ)
    (V : C(I,ℂ)) (hV : ∀ q : I, V q = γ ω ((C.horizon:ℝ)*q)) (e : ℝ) :
    observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle e
      ((BrownianDriver.path B (Real.sqrt κ) C.horizon ω,V),z) =
        (C.at z hz).physicalTime κ B γ e ω := by
  let Cz := C.at z hz
  have hs := Cz.source_live κ B ω hm hhalf hu hc hb0
  have hb := Cz.bounds κ B ω
  have ht := CompactHit.cap_eq_realTime (e := e) C.horizon_pos hb V (γ ω) z hm.1 hV hs
  rw [FiniteTilt.Cutoff.physicalTime,ht]
  simp only [observedTime,FiniteTilt.Cutoff.stopTime,FiniteTilt.Cutoff.paths,Cz,FiniteTilt.CommonCutoff.at,hr]

lemma observedTime_approach {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (ρ δ e r : ℝ)
    (U : C(I,ℝ)) (V : C(I,ℂ)) (γ : ℝ → ℂ) (hV : ∀ q : I, V q = γ (T*q)) (z : ℂ)
    (hstrict : observedTime hε hT.le ρ δ r ((U,V),z) < observedTime hε hT.le ρ δ e ((U,V),z)) :
    dist z (γ (observedTime hε hT.le ρ δ r ((U,V),z))) ≤ r := by
  have hr : CompactHit.realTime T r V z < stop hε hT.le U z ρ δ := by
    have hh : min (CompactHit.realTime T r V z) (stop hε hT.le U z ρ δ) <
        stop hε hT.le U z ρ δ := hstrict.trans_le (min_le_right _ _)
    exact (min_lt_iff.1 hh).resolve_right (lt_irrefl _)
  have ht := (stop_bounds hε hT.le U z ρ δ).2
  have hh : CompactHit.hits r (V,z) := by
    by_contra hn
    have he : CompactHit.realTime T r V z = T := by
      simp only [CompactHit.realTime,CompactHit.time_eq_one_of_not_hits hn]; simp
    rw [he] at hr
    exact (not_lt_of_ge ht) hr
  rw [observedTime,min_eq_left hr.le]
  simpa only [hV,CompactHit.realTime] using CompactHit.time_mem hh

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge.Mesh

lemma coefficient_le_poisson {z : ℂ} (hy : 0 < z.im)
    {a p s R R₀ : ℝ} (ha : 1 ≤ a) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hR₀ : 0 < R₀) (hR : R₀ ≤ R) :
    |s*a*z.re/‖z‖^2 * (R^(-p)*(z.im/‖z‖)^a)| ≤
      (s*a*R₀^(-p)) * (z.im/‖z‖^2) := by
  have hz : 0 < ‖z‖ := norm_pos_iff.2 (by intro h; simp [h] at hy)
  have hsin : 0 ≤ z.im/‖z‖ := by positivity
  have hsinle : z.im/‖z‖ ≤ 1 := (div_le_one hz).2 (Complex.im_le_norm z)
  have hpower := Real.rpow_le_self_of_le_one hsin hsinle ha
  have hr := Real.rpow_le_rpow_of_nonpos hR₀ hR (neg_nonpos.2 hp)
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hpwr : 0 ≤ R^(-p) := Real.rpow_nonneg (hR₀.le.trans hR) _
  simp only [abs_mul,abs_div,abs_of_nonneg hs,abs_of_nonneg ha0,abs_pow,abs_norm,
    abs_of_nonneg hpwr,abs_of_nonneg (Real.rpow_nonneg hsin a)]
  calc
    s*a*|z.re|/‖z‖^2*(R^(-p)*(z.im/‖z‖)^a)
        ≤ s*a*‖z‖/‖z‖^2*(R₀^(-p)*(z.im/‖z‖)) := by
          gcongr
          exact Complex.abs_re_le_norm z
    _ = (s*a*R₀^(-p))*(z.im/‖z‖^2) := by field_simp

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace SLEExactGauge.Layer

lemma hessian_scalar_comp {u : ℂ → ℝ} {φ : ℝ → ℝ} {z v : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hφ : ContDiffAt ℝ 2 φ (u z)) :
    fderiv ℝ (fderiv ℝ (φ ∘ u)) z v v =
      deriv (deriv φ) (u z)*(fderiv ℝ u z v)^2 +
        deriv φ (u z)*fderiv ℝ (fderiv ℝ u) z v v := by
  have hdu : ContDiffAt ℝ 1 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hdφ : ContDiffAt ℝ 1 (deriv φ) (u z) := hφ.derivWithin (by norm_num)
  have h₁ := ((hdφ.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt z
    (hu.differentiableAt (by norm_num)).hasFDerivAt)
  have h₂ := (hdu.differentiableAt (by norm_num)).hasFDerivAt
  have hh := h₁.smul h₂
  have he : fderiv ℝ (φ ∘ u) =ᶠ[𝓝 z] fun y => deriv φ (u y) • fderiv ℝ u y := by
    have heu : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 u y := hu.eventually (by norm_num)
    have heφ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (u y) :=
      hu.continuousAt.tendsto.eventually (hφ.eventually (by norm_num))
    filter_upwards [heu,heφ] with y hy hyφ
    exact ((hyφ.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hh' := (hh.congr_of_eventuallyEq he).fderiv
  rw [hh']
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,smul_eq_mul,Function.comp_apply]
  ring

lemma laplacian_scalar_comp {u : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hφ : ContDiffAt ℝ 2 φ (u z)) :
    Laplacian.laplacian (φ ∘ u) z =
      deriv (deriv φ) (u z)*((fderiv ℝ u z 1)^2+(fderiv ℝ u z Complex.I)^2) +
        deriv φ (u z)*Laplacian.laplacian u z := by
  rw [laplacian_eq_hessian,hessian_scalar_comp hu hφ,hessian_scalar_comp hu hφ,
    laplacian_eq_hessian]
  ring

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology RealInnerProductSpace
namespace SLEExactGauge.Layer

def diskFactor (z : ℂ) : ℝ := 1-‖z‖^2

lemma diskFactor_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < diskFactor z := by
  dsimp [diskFactor]
  nlinarith [norm_nonneg z]

lemma diskFactor_smooth : ContDiff ℝ 2 diskFactor :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

lemma diskFactor_fderiv (z : ℂ) : fderiv ℝ diskFactor z = -((2:ℝ) • innerSL ℝ z) := by
  simpa only [two_smul, diskFactor] using!
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_sub (1:ℝ)).fderiv

lemma diskFactor_hessian (z : ℂ) :
    fderiv ℝ (fderiv ℝ diskFactor) z = -((2:ℝ) • innerSL ℝ (E := ℂ)) := by
  have he : fderiv ℝ diskFactor = fun z => -((2:ℝ) • innerSL ℝ z) := funext diskFactor_fderiv
  rw [he]
  convert! ((innerSL ℝ (E := ℂ)).hasFDerivAt (x := z) |>.const_smul (2:ℝ)).neg.fderiv using 1

lemma diskFactor_gradient (z : ℂ) :
    fderiv ℝ diskFactor z 1 = -2*z.re ∧
      fderiv ℝ diskFactor z Complex.I = -2*z.im := by
  rw [diskFactor_fderiv]
  simp [Complex.inner,innerSL_apply_apply]

lemma diskFactor_laplacian (z : ℂ) : Laplacian.laplacian diskFactor z = -4 := by
  rw [laplacian_eq_hessian,diskFactor_hessian]
  simp only [neg_apply,smul_apply,smul_eq_mul]
  norm_num [innerSL,innerₛₗ,Complex.inner]

lemma logFactor_smooth {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ 2 (fun z => Real.log (diskFactor z)) z :=
  diskFactor_smooth.contDiffAt.log (ne_of_gt (diskFactor_pos hz))

end SLEExactGauge.Layer

end

end

end OAI
