import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralTime
import OAI.MathematicalPhysics.Boltzmann.Branching.FlightMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

section

/-! # The essential supremum norm along free transport -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

open FlightMeasure

def size (f : JetPrototype.Phase → ℝ) : ℝ := (eLpNorm f ∞ phaseVolume).toReal

theorem size_nonneg (f : JetPrototype.Phase → ℝ) : 0 ≤ size f := ENNReal.toReal_nonneg

theorem size_le {f : JetPrototype.Phase → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hfm : Measurable f) (hf : ∀ p, |f p| ≤ R) : size f ≤ R := by
  have he : eLpNorm f ∞ phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top hfm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

theorem size_difference {f g : JetPrototype.Phase → ℝ} {A B D : ℝ}
    (hD : 0 ≤ D) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B) (hfg : ∀ p, |f p-g p| ≤ D) :
    |size f-size g| ≤ D := by
  have hfp : MemLp f ∞ phaseVolume := memLp_top_of_bound hfm.aestronglyMeasurable A
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  have hgp : MemLp g ∞ phaseVolume := memLp_top_of_bound hgm.aestronglyMeasurable B
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hg p))
  calc
    _ = |‖hfp.toLp f‖-‖hgp.toLp g‖| := by rw [Lp.norm_toLp,Lp.norm_toLp]; rfl
    _ ≤ ‖hfp.toLp f-hgp.toLp g‖ := abs_norm_sub_norm_le _ _
    _ = size (fun p => f p-g p) := by rw [← MemLp.toLp_sub,Lp.norm_toLp]; rfl
    _ ≤ D := size_le hD (hfm.sub hgm) hfg

theorem size_flight {f : JetPrototype.Phase → ℝ} (hfm : Measurable f) (t : ℝ) :
    size (fun p => f (JetBarrier.flight t p)) = size f := by
  unfold size
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable (flight_measurePreserving t))

theorem time_difference {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    |size (fun p => f (t,p))-size (fun p => f (s,p))| ≤ (L*R+S)*(t-s) := by
  have hfs : Measurable (fun p => f (s,p)) := hfm.comp (measurable_const.prodMk measurable_id)
  have hh := size_difference (mul_nonneg (add_nonneg (mul_nonneg hL hR) hS) (sub_nonneg.mpr hst))
    (hfm.comp (measurable_const.prodMk measurable_id))
    (hfs.comp (flight_measurePreserving (s-t)).measurable)
    (fun p => hfB (t,p)) (fun p => hfB (s,JetBarrier.flight (s-t) p))
    (PositiveIntegral.along_time_bound hT hL hS hR hs hst ht hgm hg hfB hf)
  change |size (fun p => f (t,p))-size (fun p => f (s,JetBarrier.flight (s-t) p))| ≤ _ at hh
  rw [size_flight hfs] at hh
  exact hh

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Continuity of the cap ratio in the essential weighted norm -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  let C : NNReal := ⟨L*R+S,add_nonneg (mul_nonneg hL hR) hS⟩
  have hLip : LipschitzOnWith C (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    simp only [Real.dist_eq]
    change |size (fun p => f (s,p))-size (fun p => f (t,p))| ≤ (L*R+S)*|s-t|
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm (size _),abs_sub_comm s t,abs_of_nonneg (sub_nonneg.mpr hst)]
      exact time_difference hT hL hS hR hs.1 hst ht.2 hgm hfm hg hfB hf
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact time_difference hT hL hS hR ht.1 hts hs.2 hgm hfm hg hfB hf
  exact hLip.continuousOn

theorem continuousOn_ratio {T L S R δ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hδ : 0 < δ)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    ContinuousOn (fun t => size (fun p => f (t,p))/(t+δ)) (Icc 0 T) :=
  (continuousOn_size hT hL hS hR hgm hfm hg hfB hf).div
    (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))

theorem ratio_attains_max {T L S R δ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hδ : 0 < δ)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    ∃ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
      size (fun p => f (s,p))/(s+δ) ≤ size (fun p => f (t,p))/(t+δ) :=
  isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (continuousOn_ratio hT hL hS hR hδ hgm hfm hg hfB hf)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Bounded representatives that realize the essential upper bound -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem ae_abs_le_size {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ p, |f p| ≤ R) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ size f := by
  have hm : MemLp f ∞ FlightMeasure.phaseVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hf p))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm,size] using ae_le_lpNorm_exponent_top hm

theorem size_le_ae {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ R) : size f ≤ R := by
  have h : eLpNorm f ∞ FlightMeasure.phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top hfm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (hf.mono (fun p hp => by
      simpa only [Real.norm_eq_abs] using hp))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

def canonical (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  min (f u) (size (fun p => f (u.1,p)))

theorem measurable_canonical {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    (hnorm : Measurable (fun t => size (fun p => f (t,p)))) : Measurable (canonical f) :=
  hfm.min (hnorm.comp measurable_fst)

theorem canonical_bounds {f : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ u, 0 ≤ f u) (u : ℝ × JetPrototype.Phase) :
    0 ≤ canonical f u ∧ canonical f u ≤ size (fun p => f (u.1,p)) ∧ canonical f u ≤ f u :=
  ⟨le_min (hf u) (size_nonneg _),min_le_right _ _,min_le_left _ _⟩

theorem canonical_ae_at_time {f : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) {R : ℝ} (hf : ∀ u, |f u| ≤ R) (t : ℝ) :
    (fun p => canonical f (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => f (t,p)) := by
  filter_upwards [ae_abs_le_size (hfm.comp (measurable_const.prodMk measurable_id))
    (fun p => hf (t,p))] with p hp
  exact min_eq_left ((le_abs_self _).trans hp)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Stability of the essential norm under a.e. bounded differences -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_difference_ae {f g : JetPrototype.Phase → ℝ} {A B D : ℝ}
    (hD : 0 ≤ D) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B)
    (hfg : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p-g p| ≤ D) :
    |size f-size g| ≤ D := by
  have hfp : MemLp f ∞ FlightMeasure.phaseVolume := memLp_top_of_bound
    hfm.aestronglyMeasurable A (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  have hgp : MemLp g ∞ FlightMeasure.phaseVolume := memLp_top_of_bound
    hgm.aestronglyMeasurable B (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hg p))
  calc
    _ = |‖hfp.toLp f‖-‖hgp.toLp g‖| := by rw [Lp.norm_toLp,Lp.norm_toLp]; rfl
    _ ≤ ‖hfp.toLp f-hgp.toLp g‖ := abs_norm_sub_norm_le _ _
    _ = size (fun p => f p-g p) := by rw [← MemLp.toLp_sub,Lp.norm_toLp]; rfl
    _ ≤ D := size_le_ae (hfm.sub hgm) hD hfg

theorem hot_difference_ae {I : Type*} [Countable I]
    {F G : JetPrototype.Phase → ℝ} {c d : I → JetPrototype.Phase → ℝ}
    {R D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hG : ∀ p, 0 ≤ G p ∧ G p ≤ R)
    (hcn : ∀ i p, 0 ≤ c i p) (hdn : ∀ i p, 0 ≤ d i p)
    (hcSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (hdSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, d i p ≤ G p)
    (hFG : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F p-G p| ≤ D)
    (hcd : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i p-d i p|) ≤ E) :
    |size (fun p => F p-∑' i, c i p)-size (fun p => G p-∑' i, d i p)| ≤ D+E := by
  have hcs (p) : Summable (fun i => c i p) := summable_of_sum_le
    (fun i => hcn i p) (fun s => hcSum s p)
  have hds (p) : Summable (fun i => d i p) := summable_of_sum_le
    (fun i => hdn i p) (fun s => hdSum s p)
  have hcb (p) : |F p-∑' i, c i p| ≤ R := by
    have hn : 0 ≤ ∑' i, c i p := tsum_nonneg (fun i => hcn i p)
    have hs := Real.tsum_le_of_sum_le (fun i => hcn i p) (fun s => hcSum s p)
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [(hF p).2]
  have hdb (p) : |G p-∑' i, d i p| ≤ R := by
    have hn : 0 ≤ ∑' i, d i p := tsum_nonneg (fun i => hdn i p)
    have hs := Real.tsum_le_of_sum_le (fun i => hdn i p) (fun s => hdSum s p)
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [(hG p).2]
  apply size_difference_ae (add_nonneg hD hE)
    (hFm.sub (Measurable.tsum hcm)) (hGm.sub (Measurable.tsum hdm)) hcb hdb
  filter_upwards [hFG,hcd] with p hp hcp
  have ht : |(∑' i, c i p)-(∑' i, d i p)| ≤ E := by
    rw [← (hcs p).tsum_sub (hds p)]
    have hn : Summable (fun i : I => ‖c i p - d i p‖) := by
      simpa only [Real.norm_eq_abs] using ((hcs p).sub (hds p)).abs
    have ha : |tsum (fun i : I => c i p - d i p)| ≤ tsum (fun i : I => |c i p - d i p|) := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    exact ha.trans hcp
  have he : (F p-∑' i, c i p)-(G p-∑' i, d i p) =
      (F p-G p)-((∑' i, c i p)-(∑' i, d i p)) := by ring
  change |(F p-∑' i, c i p)-(G p-∑' i, d i p)| ≤ D+E
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hp ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Scalar upper integral bounds for the essential norm of a mild solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem value_le_ae {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S) (hw : IntervalIntegrable w volume 0 T)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p) ≤
        Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  have hi := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae hinit
  have hs := (FlightMeasure.spacetime_measurePreserving t).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  have hwt : IntervalIntegrable w volume 0 t := hw.mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2)
  have hwi : IntervalIntegrable (fun r => Real.exp (-L*(t-r))*w r) volume 0 t :=
    hwt.continuousOn_mul (by fun_prop)
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  rw [GaussianLocal.time_eq ht]
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  have hgi := PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
  rw [GaussianLocal.time_eq ht] at hgi
  apply intervalIntegral.integral_mono_ae_restrict ht.1 hgi hwi
  filter_upwards [ae_restrict_of_ae hrp,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with r hr hrmem hr0
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hr ⟨lt_of_le_of_ne hrmem.1 hr0.symm,hrmem.2.trans ht.2⟩

theorem mild_size_le {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (ha : 0 ≤ a) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hw : IntervalIntegrable w volume 0 T) (hwn : ∀ r ∈ Icc 0 T, 0 ≤ w r)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1)
    (hfn : ∀ u, 0 ≤ f u)
    (hfix : ∀ u, f u = PositiveIntegral.value T L JetBarrier.flight f₀ g u) :
    size (fun p => f (t,p)) ≤ Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  apply size_le_ae (f := fun p => f (t,p)) (hfm.comp (measurable_const.prodMk measurable_id))
  · apply add_nonneg (mul_nonneg (Real.exp_pos _).le ha)
    apply intervalIntegral.integral_nonneg ht.1
    intro r hr
    exact mul_nonneg (Real.exp_pos _).le (hwn r ⟨hr.1,hr.2.trans ht.2⟩)
  · filter_upwards [value_le_ae hT hL ht hgm hg hw hinit hsource] with p hp
    rw [abs_of_nonneg (hfn (t,p)),hfix (t,p)]
    exact hp

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Global norm continuity for the clamped local construction -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem time_idempotent {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    PositiveIntegral.time T (PositiveIntegral.time T t) = PositiveIntegral.time T t :=
  GaussianLocal.time_eq (PositiveIntegral.time_bounds hT t)

theorem continuous_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S) (hfB : ∀ u, |f u| ≤ R)
    (hf : ∀ u, f u = PositiveIntegral.value T L JetBarrier.flight f₀ g u) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  have he (t : ℝ) (p : JetPrototype.Phase) :
      f (t,p) = f (PositiveIntegral.time T t,p) := by
    rw [hf (t,p),hf (PositiveIntegral.time T t,p)]
    simp only [PositiveIntegral.value,time_idempotent hT]
  have hn : (fun t => size (fun p => f (t,p))) =
      (fun t => size (fun p => f (PositiveIntegral.time T t,p))) := by
    funext t
    exact congrArg size (funext (he t))
  rw [hn]
  exact (continuousOn_size hT hL hS hR hgm hfm hg hfB hf).comp_continuous
    (by unfold PositiveIntegral.time; fun_prop) (PositiveIntegral.time_bounds hT)

theorem canonical_ae {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ u, |f u| ≤ R)
    (hnorm : Measurable (fun t => size (fun p => f (t,p)))) :
    canonical f =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] f := by
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun (measurable_canonical hfm hnorm) hfm)).mpr
  exact ae_of_all _ (canonical_ae_at_time hfm hf)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Essential-norm estimates for mild equations holding almost everywhere -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_congr_ae {f g : JetPrototype.Phase → ℝ}
    (hfg : f =ᵐ[FlightMeasure.phaseVolume] g) : size f = size g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

theorem continuous_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  let v := PositiveIntegral.value T L JetBarrier.flight f₀ g
  have hvm : Measurable v := PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hf₀m hgm
  have hv (u) := PositiveIntegral.value_bounds hT hL hA hS JetBarrier.flight hf₀ hg u
  have hga (u) : |g u| ≤ S := by rw [abs_of_nonneg (hg u).1]; exact (hg u).2
  have hva (u) : |v u| ≤ A+T*S := by rw [abs_of_nonneg (hv u).1]; exact (hv u).2
  have he : (fun t => size (fun p => f (t,p))) = (fun t => size (fun p => v (t,p))) :=
    funext (fun t => size_congr_ae (hfix t))
  rw [he]
  exact continuous_size hT hL hS (by positivity) hgm hvm hga hva (fun _ => rfl)

theorem mild_size_le_of_ae {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hw : IntervalIntegrable w volume 0 T) (hwn : ∀ r ∈ Icc 0 T, 0 ≤ w r)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1)
    (hfn : ∀ u, 0 ≤ f u)
    (hfix : (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    size (fun p => f (t,p)) ≤ Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  apply size_le_ae (f := fun p => f (t,p)) (hfm.comp (measurable_const.prodMk measurable_id))
  · apply add_nonneg (mul_nonneg (Real.exp_pos _).le ha)
    exact intervalIntegral.integral_nonneg ht.1 (fun r hr =>
      mul_nonneg (Real.exp_pos _).le (hwn r ⟨hr.1,hr.2.trans ht.2⟩))
  · filter_upwards [value_le_ae hT hL ht hgm hg hw hinit hsource,hfix] with p hp he
    rw [abs_of_nonneg (hfn (t,p)),he]
    exact hp

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Bounding a total essential norm by its cold and hot parts -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_le_cold_add_hot {f c : JetPrototype.Phase → ℝ} {R B Z : ℝ}
    (hfm : Measurable f) (hcm : Measurable c) (hB : 0 ≤ B)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ f p)
    (hcB : ∀ p, c p ≤ B) (hz : size (fun p => f p-c p) ≤ Z) :
    size f ≤ B+Z := by
  have habs (p) : |f p-c p| ≤ R := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hc p).2)]
    linarith [(hf p).2,(hc p).1]
  have hZ : 0 ≤ Z := (size_nonneg _).trans hz
  apply size_le_ae hfm (add_nonneg hB hZ)
  filter_upwards [ae_abs_le_size (hfm.sub hcm) habs] with p hp
  change |f p-c p| ≤ size (fun p => f p-c p) at hp
  rw [abs_of_nonneg (hf p).1]
  rw [abs_of_nonneg (sub_nonneg.mpr (hc p).2)] at hp
  linarith [hcB p]

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
