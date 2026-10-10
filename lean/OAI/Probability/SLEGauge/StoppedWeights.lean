import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ReverseGenerators
import OAI.Probability.SLEGauge.RadialBounds

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
lemma regionStop_weight_eq (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver)
    (hr : physicalRadius (localState a ε hε z (regionStop a ε hε z N ρ δ B b) b) = ρ) :
    physicalGreen a (localState a ε hε z (regionStop a ε hε z N ρ δ B b) b) =
      radialWeight a b.1 z ρ := by
  have he := regionStop_eq_radialTime a ε hε z N ρ δ B h0 b hr
  rw [radialWeight,he,ite_eq_right ENNReal.coe_ne_top,ENNReal.toNNReal_coe]
  rw [(regionStop_actualState a ε hε z N ρ δ B h0 b _ le_rfl).2]

lemma actual_sine_lower (a : ℝ) (b : ℝ≥0 → ℝ) (hb : Continuous b) (z : ℂ)
    (T : ℝ≥0) (hT : alive a b T z) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ≥0, t ≤ T →
      η ≤ Y (actualState a b t z) / ‖(actualState a b t z).1‖ := by
  obtain ⟨f,hf⟩ := hT
  let s : ℝ → ℝ := fun u => (f u).im / ‖f u-(b u.toNNReal : ℂ)‖
  have hnp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : 0 < ‖f u-(b u.toNNReal : ℂ)‖ :=
    norm_pos_iff.mpr (odeUntil_center_ne_zero hf hu)
  have hsc : ContinuousOn s (Icc (0 : ℝ) T) :=
    (Complex.continuous_im.comp_continuousOn (odeUntil_continuousOn hf)).div
      (odeUntil_center_continuousOn hb hf).norm (fun u hu => (hnp u hu).ne')
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr T.coe_nonneg) hsc
  refine ⟨s u,div_pos (hf.2 u hu).1 (hnp u hu),?_⟩
  intro t ht
  have hv : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg,ht⟩
  have hl := hmin hv
  change s u ≤ s (t : ℝ) at hl
  have he : loewnerMap a b t z = f t := by
    simpa only [Real.toNNReal_coe] using loewnerMap_eq_solution_time hf hv
  simpa only [s,actualState,Y_apply,he,
    Real.toNNReal_coe,Complex.sub_im,Complex.ofReal_im,sub_zero] using hl

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

 

structure RadialLocalization (a : ℝ) (z : ℂ) (ρ δ : ℝ) where
  ε : ℝ
  hε : 0 < ε
  N : ℝ≥0
  B : ℝ≥0
  initial : 0 ≤ regionMonitor ε N ρ δ (z,0)
  small : ε < heightFloor z.im ρ δ
  large : z.im/δ+logCeiling z.im ρ δ < N
  time : z.im^2 < 2*a*δ^2*(B : ℝ)

lemma exists_radialLocalization (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (hδ : 0 < δ)
    (hs : δ*‖z‖ ≤ z.im) : Nonempty (RadialLocalization a z ρ δ) := by
  let m := heightFloor z.im ρ δ
  let C := logCeiling z.im ρ δ
  have hm : 0 < m := heightFloor_pos _ _ _
  have hC : 0 ≤ C := logCeiling_nonneg _ _ _
  have hmz : m ≤ z.im := heightFloor_le hz hρ hr
  let N : ℝ≥0 := ⟨z.im/δ+C+1,by positivity⟩
  let B : ℝ≥0 := ⟨z.im^2/(2*a*δ^2)+1,by positivity⟩
  have hinit : 0 ≤ regionMonitor (m/2) N ρ δ (z,0) := by
    apply (regionMonitor_nonneg_iff _ _ _ _ _).mpr
    have hnorm : ‖z‖ ≤ z.im/δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hs)
    refine ⟨?_,?_,?_,hs⟩
    · change m/2 ≤ z.im
      linarith
    · simpa only [Prod.norm_def,Real.norm_eq_abs,abs_zero,max_eq_left (norm_nonneg z)] using
        (show ‖z‖ ≤ (N : ℝ) by change ‖z‖ ≤ z.im/δ+C+1; linarith)
    · simpa only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one] using hr
  refine ⟨⟨m/2,by positivity,N,B,hinit,by change m/2 < m; linarith,?_,?_⟩⟩
  · change z.im/δ+C < z.im/δ+C+1
    linarith
  · change z.im^2 < 2*a*δ^2*(z.im^2/(2*a*δ^2)+1)
    have hp : 0 < 2*a*δ^2 := by positivity
    field_simp
    nlinarith

noncomputable def radialLocalization (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (hδ : 0 < δ)
    (hs : δ*‖z‖ ≤ z.im) : RadialLocalization a z ρ δ :=
  Classical.choice (exists_radialLocalization a ha z hz ρ δ hρ hr hδ hs)

noncomputable def angleThreshold (z : ℂ) (n : ℕ) : ℝ :=
  (z.im/‖z‖) / ((n : ℝ)+1)
lemma angleThreshold_pos (z : ℂ) (hz : 0 < z.im) (n : ℕ) : 0 < angleThreshold z n := by
  have hn : 0 < ‖z‖ := hz.trans_le (Complex.im_le_norm z)
  unfold angleThreshold
  positivity
lemma angleThreshold_initial (z : ℂ) (hz : 0 < z.im) (n : ℕ) :
    angleThreshold z n * ‖z‖ ≤ z.im := by
  have hn : 0 < ‖z‖ := hz.trans_le (Complex.im_le_norm z)
  have hle : angleThreshold z n ≤ z.im/‖z‖ := by
    exact div_le_self (div_nonneg hz.le hn.le) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  exact (mul_le_mul_of_nonneg_right hle hn.le).trans_eq (div_mul_cancel₀ _ hn.ne')
lemma angleThreshold_tendsto (z : ℂ) : Tendsto (angleThreshold z) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (z.im/‖z‖)/((n : ℝ)+1)) atTop (𝓝 0)
  simpa only [mul_one_div,mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (z.im/‖z‖)

noncomputable def radialApproximation (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) (b : ExactSLEGenerator.Driver) : ℝ :=
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  physicalGreen a (localState a L.ε L.hε z
    (regionStop a L.ε L.hε z L.N ρ (angleThreshold z n) L.B b) b)

lemma radialApproximation_mean (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) :
    Integrable (radialApproximation a ha z hz ρ hρ hr n) W ∧
      (∫ b, radialApproximation a ha z hz ρ hρ hr n b ∂W) = physicalGreen a (z,0) := by
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  exact regionStop_green_mean W hW a L.ε ha.ne' L.hε z L.N L.B ρ (angleThreshold z n) L.initial

lemma radialApproximation_bound (a : ℝ) (ha : 1/4 < a) (ha0 : 0 < a) (z : ℂ)
    (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ)
    (b : ExactSLEGenerator.Driver) :
    0 ≤ radialApproximation a ha0 z hz ρ hρ hr n b ∧
      radialApproximation a ha0 z hz ρ hρ hr n b ≤ Real.exp (-alpha a*Real.log ρ) := by
  let L := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b _ le_rfl
  exact ⟨(Real.exp_pos _).le,physicalGreen_bound a ρ ha hρ _ (L.hε.trans_le hs.1) hs.2.2.1⟩

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma physicalGreen_angle_bound (a ρ δ : ℝ) (ha : 1/4 < a) (hρ : 0 < ρ)
    (v : State) (hy : 0 < Y v) (hr : ρ ≤ physicalRadius v)
    (hs : Y v = δ*‖v.1‖) :
    physicalGreen a v ≤ Real.exp (-alpha a*Real.log ρ) * δ^(p a) := by
  have hn : 0 < ‖v.1‖ := hy.trans_le (Complex.im_le_norm _)
  have hd : Y v / ‖v.1‖ = δ := (div_eq_iff hn.ne').mpr hs
  rw [physicalGreen_eq_radius_sine a v hy,hd]
  have hR : 0 < physicalRadius v := hρ.trans_le hr
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by
    rw [← hd]; exact div_nonneg hy.le hn.le) _)
  rw [Real.rpow_def_of_pos hR]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_log hρ hr
  nlinarith [mul_le_mul_of_nonneg_left hlog (alpha_pos ha).le]

lemma radialApproximation_tendsto (a : ℝ) (ha : 1/4 < a) (ha0 : 0 < a)
    (z : ℂ) (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (b : ExactSLEGenerator.Driver) :
    Tendsto (fun n => radialApproximation a ha0 z hz ρ hρ hr n b) atTop
      (𝓝 (radialWeight a b.1 z ρ)) := by
  classical
  let L (n : ℕ) := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T (n : ℕ) := regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b
  let V (n : ℕ) := localState a (L n).ε (L n).hε z (T n) b
  have hexit (n : ℕ) : physicalRadius (V n) = ρ ∨ Y (V n) = angleThreshold z n*‖(V n).1‖ :=
    regionStop_true_exit a (L n).ε ha0 (L n).hε z (L n).N ρ (angleThreshold z n)
      hρ (angleThreshold_pos z hz n) (L n).B (L n).initial (L n).small (L n).large (L n).time b
  have hactual (n : ℕ) : alive a b.1 (T n) z ∧ actualState a b.1 (T n) z = V n :=
    regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
      (L n).B (L n).initial b _ le_rfl
  by_cases hex : ∃ t : ℝ≥0, alive a b.1 t z ∧ physicalRadius (actualState a b.1 t z) = ρ
  · obtain ⟨t,ht,htr⟩ := hex
    obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht
    have he : ∀ᶠ n in atTop, radialApproximation a ha0 z hz ρ hρ hr n b = radialWeight a b.1 z ρ := by
      filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
      have ht' : T n ≤ t := regionStop_le_hit a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
        (L n).B (L n).initial b t htr
      have hη' := hηs (T n) ht'
      rw [(hactual n).2] at hη'
      rcases hexit n with hR|hS
      · exact regionStop_weight_eq a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b hR
      · have hsafe := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b (T n) le_rfl
        have hnp : 0 < ‖(V n).1‖ := ((L n).hε.trans_le hsafe.1).trans_le (Complex.im_le_norm _)
        have hd : Y (V n)/‖(V n).1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
        rw [hd] at hη'
        exact False.elim (not_le.mpr hn hη')
    exact Filter.Tendsto.congr' (he.mono fun n hn => hn.symm) tendsto_const_nhds
  · have hw : radialWeight a b.1 z ρ = 0 := by rw [radialWeight,ite_eq_left (radialTime_top_of_no_hit a b.1 z ρ hex)]
    rw [hw]
    have hbound (n : ℕ) : radialApproximation a ha0 z hz ρ hρ hr n b ≤
        Real.exp (-alpha a*Real.log ρ) * (angleThreshold z n)^(p a) := by
      rcases hexit n with hR|hS
      · exact False.elim (hex ⟨T n,(hactual n).1,by simpa only [(hactual n).2] using hR⟩)
      · have hs := regionStop_safe a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n)
          (L n).B (L n).initial b (T n) le_rfl
        exact physicalGreen_angle_bound a ρ (angleThreshold z n) ha hρ (V n)
          ((L n).hε.trans_le hs.1) hs.2.2.1 hS
    have hp : 0 < p a := by unfold p; linarith
    have hu : Tendsto (fun n => Real.exp (-alpha a*Real.log ρ) * (angleThreshold z n)^(p a)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ((angleThreshold_tendsto z).rpow_const_nhds_zero hp).const_mul
        (Real.exp (-alpha a*Real.log ρ))
    exact squeeze_zero (fun n => (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).1) hbound hu

 

theorem radialWeight_mean (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) :
    Integrable (fun b : ExactSLEGenerator.Driver => radialWeight a b.1 z ρ) W ∧
      (∫ b : ExactSLEGenerator.Driver, radialWeight a b.1 z ρ ∂W) = physicalGreen a (z,0) := by
  have ha0 : 0 < a := by linarith
  let F := radialApproximation a ha0 z hz ρ hρ hr
  let G := fun b : ExactSLEGenerator.Driver => radialWeight a b.1 z ρ
  let C := Real.exp (-alpha a*Real.log ρ)
  have hFi (n : ℕ) : Integrable (F n) W := (radialApproximation_mean W hW a ha0 z hz ρ hρ hr n).1
  have hconv (b : ExactSLEGenerator.Driver) : Tendsto (fun n => F n b) atTop (𝓝 (G b)) :=
    radialApproximation_tendsto a ha ha0 z hz ρ hρ hr b
  have hFm (n : ℕ) := (hFi n).aestronglyMeasurable
  have hGm : AEStronglyMeasurable G W := aestronglyMeasurable_of_tendsto_ae atTop hFm
    (Eventually.of_forall hconv)
  have hFb (n : ℕ) : ∀ᵐ b ∂W, ‖F n b‖ ≤ C := by
    filter_upwards [] with b
    have h := radialApproximation_bound a ha ha0 z hz ρ hρ hr n b
    change ‖radialApproximation a ha0 z hz ρ hρ hr n b‖ ≤ Real.exp (-alpha a*Real.log ρ)
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  have hGb : ∀ᵐ b ∂W, ‖G b‖ ≤ C := by
    filter_upwards [] with b
    exact le_of_tendsto (hconv b).norm (Eventually.of_forall fun n => by
      have h := radialApproximation_bound a ha ha0 z hz ρ hρ hr n b
      change ‖radialApproximation a ha0 z hz ρ hρ hr n b‖ ≤ Real.exp (-alpha a*Real.log ρ)
      simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2)
  have hGi : Integrable G W := Integrable.of_bound hGm C hGb
  refine ⟨hGi,?_⟩
  have hi := tendsto_integral_of_dominated_convergence (fun _ => C) hFm
    (integrable_const C) hFb (Eventually.of_forall hconv)
  have he : (fun n => ∫ b, F n b ∂W) = fun _ : ℕ => physicalGreen a (z,0) :=
    funext fun n => (radialApproximation_mean W hW a ha0 z hz ρ hρ hr n).2
  rw [he] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma radialTime_attained (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver)
    (hfin : radialTime a b.1 z ρ ≠ ∞) :
    alive a b.1 (radialTime a b.1 z ρ).toNNReal z ∧
      physicalRadius (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z) = ρ := by
  have hex : ∃ t : ℝ≥0, alive a b.1 t z ∧ physicalRadius (actualState a b.1 t z) = ρ := by
    by_contra hn
    exact hfin (radialTime_top_of_no_hit a b.1 z ρ hn)
  obtain ⟨t,ht,htr⟩ := hex
  obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht
  obtain ⟨n,hn⟩ := ((angleThreshold_tendsto z).eventually (gt_mem_nhds hη)).exists
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := regionStop a L.ε L.hε z L.N ρ (angleThreshold z n) L.B b
  let V := localState a L.ε L.hε z T b
  have he := regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
  have ht' : T ≤ t := regionStop_le_hit a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t htr
  have hR : physicalRadius V = ρ := by
    rcases regionStop_true_exit a L.ε ha L.hε z L.N ρ (angleThreshold z n)
      hρ (angleThreshold_pos z hz n) L.B L.initial L.small L.large L.time b with hR|hS
    · exact hR
    · have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
      have hnp : 0 < ‖V.1‖ := (L.hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
      have hd : Y V/‖V.1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
      have hη' := hηs T ht'
      rw [he.2,hd] at hη'
      exact False.elim (not_le.mpr hn hη')
  have htime := regionStop_eq_radialTime a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b hR
  rw [htime,ENNReal.toNNReal_coe]
  change alive a b.1 T z ∧ physicalRadius (actualState a b.1 T z) = ρ
  exact ⟨he.1,by rw [he.2]; exact hR⟩

end ExactSLEGreen

open Filter
open scoped Topology
namespace ExactSLEMain
noncomputable def diskMap (θ : ℝ) (z : ℂ) : ℂ :=
  (z - Complex.exp (Complex.I * θ)) / (z - Complex.exp (-Complex.I * θ))
noncomputable def fromDisk (θ : ℝ) (x : ℂ) : ℂ :=
  (x * Complex.exp (-Complex.I * θ) - Complex.exp (Complex.I * θ)) / (x - 1)

lemma fromDisk_zero (θ : ℝ) : fromDisk θ 0 = Complex.exp (Complex.I*θ) := by simp [fromDisk]
lemma fromDisk_zero_im (θ : ℝ) : (fromDisk θ 0).im = Real.sin θ := by
  rw [fromDisk_zero,mul_comm,Complex.exp_ofReal_mul_I_im]
lemma fromDisk_zero_norm (θ : ℝ) : ‖fromDisk θ 0‖ = 1 := by
  rw [fromDisk_zero,Complex.norm_exp]
  simp
lemma disk_endpoints_difference (θ : ℝ) :
    Complex.exp (Complex.I*θ)-Complex.exp (-Complex.I*θ) = (2*Real.sin θ : ℝ)*Complex.I := by
  rw [mul_comm Complex.I,show -Complex.I*(θ : ℂ) = ((-θ : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  push_cast
  ring
lemma disk_endpoints_ne (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Complex.exp (Complex.I*θ)-Complex.exp (-Complex.I*θ) ≠ 0 := by
  rw [disk_endpoints_difference]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)).ne') Complex.I_ne_zero
lemma disk_deriv_at_zero (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    deriv (diskMap θ) (fromDisk θ 0) =
      (Complex.exp (Complex.I*θ)-Complex.exp (-Complex.I*θ))⁻¹ := by
  rw [fromDisk_zero]
  have hn := disk_endpoints_ne θ hθ hθπ
  have hd := ((hasDerivAt_id (Complex.exp (Complex.I*θ))).sub_const (Complex.exp (Complex.I*θ))).div
    ((hasDerivAt_id (Complex.exp (Complex.I*θ))).sub_const (Complex.exp (-Complex.I*θ))) hn
  change deriv (fun z => (z-Complex.exp (Complex.I*θ))/(z-Complex.exp (-Complex.I*θ))) _ = _
  have hd' := hd.deriv
  change deriv (fun z => (z-Complex.exp (Complex.I*θ))/(z-Complex.exp (-Complex.I*θ))) _ = _ at hd'
  rw [hd']
  simp only [id_eq,sub_self,zero_mul,sub_zero,one_mul]
  field_simp [hn]
lemma disk_deriv_norm (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ‖deriv (diskMap θ) (fromDisk θ 0)‖ = (2*Real.sin θ)⁻¹ := by
  rw [disk_deriv_at_zero θ hθ hθπ,disk_endpoints_difference,norm_inv,norm_mul,Complex.norm_real,
    Complex.norm_I,mul_one,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))]
end ExactSLEMain

namespace ExactSLEMain
noncomputable def centeredZ (A : ℝ) (θ : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℂ) : ℂ :=
  loewnerMap A b t (fromDisk θ x) - (b t : ℂ)
noncomputable def sineAngle (A θ : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℂ) : ℝ :=
  (centeredZ A θ b t x).im / ‖centeredZ A θ b t x‖
noncomputable def diskRadius (A θ : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℂ) : ℝ :=
  ‖deriv (diskMap θ) (fromDisk θ x)‖ * (2 * (centeredZ A θ b t x).im) /
    ‖deriv (loewnerMap A b t) (fromDisk θ x)‖
noncomputable def green (a θ : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℂ) : ℝ := by
  classical
  exact if alive a b t (fromDisk θ x) then
    diskRadius a θ b t x ^ (-(2 - (1 + 1 / (4 * a)))) * sineAngle a θ b t x ^ (4 * a - 1)
    else 0

noncomputable def levelTime (a θ : ℝ) (b : ℝ≥0 → ℝ) (l : ℕ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ t : ℝ≥0, u = t ∧ alive a b t (fromDisk θ 0) ∧
    diskRadius a θ b t 0 = Real.exp (-2 * a * l)}
noncomputable def tiltWeight (a θ : ℝ) (b : ℝ≥0 → ℝ) (l : ℕ) : ℝ :=
  if levelTime a θ b l = ∞ then 0 else
    Real.exp (2 * a * (2 - (1 + 1 / (4 * a))) * l) *
      sineAngle a θ b (levelTime a θ b l).toNNReal 0 ^ (4 * a - 1) / Real.sin θ ^ (4 * a - 1)

end ExactSLEMain

namespace ExactSLEMain
open ExactSLEGreen

lemma diskRadius_actualState (a θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (b : ℝ≥0 → ℝ) (hb : Continuous b) (t : ℝ≥0)
    (ht : alive a b t (fromDisk θ 0)) :
    diskRadius a θ b t 0 = physicalRadius (actualState a b t (fromDisk θ 0)) / Real.sin θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hd : 0 < ‖deriv (loewnerMap a b t) (fromDisk θ 0)‖ :=
    norm_pos_iff.mpr (deriv_loewnerMap_ne_zero hb ht)
  unfold diskRadius physicalRadius actualState centeredZ
  rw [disk_deriv_norm θ hθ hθπ]
  simp only [Y_apply,J_apply,Real.exp_neg,Real.exp_log hd]
  field_simp

lemma levelTime_radialTime (a θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (b : ℝ≥0 → ℝ) (hb : Continuous b) (l : ℕ) :
    levelTime a θ b l = radialTime a b (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  unfold levelTime radialTime
  congr 1
  ext u
  constructor
  · rintro ⟨t,hu,ht,hR⟩
    refine ⟨t,hu,ht,?_⟩
    rw [diskRadius_actualState a θ hθ hθπ b hb t ht] at hR
    simpa only [mul_comm] using (div_eq_iff hs.ne').mp hR
  · rintro ⟨t,hu,ht,hR⟩
    refine ⟨t,hu,ht,?_⟩
    rw [diskRadius_actualState a θ hθ hθπ b hb t ht,hR,mul_div_cancel_left₀ _ hs.ne']

lemma radial_initial_green (a θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    physicalGreen a (fromDisk θ 0,0) =
      (Real.sin θ)^(-alpha a)*(Real.sin θ)^(p a) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  rw [physicalGreen_eq_radius_sine a _ (by simpa only [Y_apply,fromDisk_zero_im] using hs)]
  simp only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one,fromDisk_zero_im,
    fromDisk_zero_norm,div_one]

lemma tiltWeight_radialWeight (a θ : ℝ) (ha : 1/4 < a) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (b : Driver) (l : ℕ) :
    tiltWeight a θ b.1 l =
      radialWeight a b.1 (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)) /
        physicalGreen a (fromDisk θ 0,0) := by
  have ha0 : 0 < a := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  let ρ := Real.sin θ*Real.exp (-2*a*l)
  have hρ : 0 < ρ := mul_pos hs (Real.exp_pos _)
  have hr : ρ ≤ (fromDisk θ 0).im := by
    rw [fromDisk_zero_im]
    have he : Real.exp (-2*a*l) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have h : (0 : ℝ) ≤ 2*a*l := by positivity
      nlinarith)
    exact (mul_le_mul_of_nonneg_left he hs.le).trans_eq (mul_one _)
  have hz : 0 < (fromDisk θ 0).im := by simpa only [fromDisk_zero_im] using hs
  have htime := levelTime_radialTime a θ hθ hθπ b.1 b.1.continuous l
  by_cases hfin : radialTime a b.1 (fromDisk θ 0) ρ = ∞
  · rw [tiltWeight,htime,ite_eq_left hfin,radialWeight,ite_eq_left hfin,zero_div]
  · have ht := radialTime_attained a ha0 (fromDisk θ 0) hz ρ hρ hr b hfin
    let T := (radialTime a b.1 (fromDisk θ 0) ρ).toNNReal
    have hy : 0 < Y (actualState a b.1 T (fromDisk θ 0)) := by
      obtain ⟨f,hf⟩ := ht.1
      rw [Y_apply,actualState,Complex.sub_im,Complex.ofReal_im,sub_zero,loewnerMap_eq hf]
      exact (hf.2 T ⟨T.coe_nonneg,le_rfl⟩).1
    have heα : 2-(1+1/(4*a)) = alpha a := by unfold alpha; ring
    rw [tiltWeight,htime,ite_eq_right hfin,radialWeight,ite_eq_right hfin,
      physicalGreen_eq_radius_sine a _ hy,ht.2,radial_initial_green a θ hθ hθπ,heα]
    change Real.exp (2*a*alpha a*l)*
        (Y (actualState a b.1 T (fromDisk θ 0))/‖(actualState a b.1 T (fromDisk θ 0)).1‖)^(p a) /
        (Real.sin θ)^(p a) =
      ρ^(-alpha a)*(Y (actualState a b.1 T (fromDisk θ 0))/‖(actualState a b.1 T (fromDisk θ 0)).1‖)^(p a) /
        ((Real.sin θ)^(-alpha a)*(Real.sin θ)^(p a))
    have he : ρ^(-alpha a) = (Real.sin θ)^(-alpha a)*Real.exp (2*a*alpha a*l) := by
      rw [Real.rpow_def_of_pos hρ,Real.rpow_def_of_pos hs]
      dsimp only [ρ]
      rw [Real.log_mul hs.ne' (Real.exp_ne_zero _),Real.log_exp,← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hn : (Real.sin θ)^(-alpha a) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
    field_simp

 

end ExactSLEMain
end

end OAI
