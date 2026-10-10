import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralTime
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.FlightMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence

namespace OAI

section

/-! # Subtracting two bounded characteristic integral equations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_sub {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {g h : ℝ × JetPrototype.Phase → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (f₀ k₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u-value T L JetBarrier.flight k₀ h u =
      value T L JetBarrier.flight (fun p => f₀ p-k₀ p) (fun z => g z-h z) u := by
  unfold value
  have he (r : ℝ) : Real.exp (-L*(time T u.1-r)) *
      (g (r,JetBarrier.flight (r-time T u.1) u.2)-h (r,JetBarrier.flight (r-time T u.1) u.2)) =
      Real.exp (-L*(time T u.1-r))*g (r,JetBarrier.flight (r-time T u.1) u.2)-
        Real.exp (-L*(time T u.1-r))*h (r,JetBarrier.flight (r-time T u.1) u.2) := mul_sub _ _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (damped_integrable hT hL GaussianLocal.measurable_flight hgm hg u)
    (damped_integrable hT hL GaussianLocal.measurable_flight hhm hh u)]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # The positive integral only uses source values on its time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_eq_of_time_eq {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) {g h : ℝ × JetPrototype.Phase → ℝ}
    (hgh : ∀ r ∈ Icc 0 T, ∀ p, g (r,p) = h (r,p)) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u = value T L JetBarrier.flight f₀ h u := by
  unfold value
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (time_bounds hT u.1).1] at hr
  dsimp only
  rw [hgh r ⟨hr.1,hr.2.trans (time_bounds hT u.1).2⟩]

theorem value_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (time T u.1,u.2) = value T L JetBarrier.flight f₀ g u := by
  simp only [value,PhaseEssSup.time_idempotent hT]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Almost-everywhere difference bounds for the damped characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_difference_initial_ae {T L S D I t : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I) (ht : t ∈ Icc 0 T)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-k₀ p| ≤ I)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, |g u-h u| ≤ D) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |value T L JetBarrier.flight f₀ g (t,p)-value T L JetBarrier.flight k₀ h (t,p)| ≤ I+T*D := by
  have hdiff (u) : |g u-h u| ≤ 2*S := (abs_sub _ _).trans (by linarith [hg u,hh u])
  have hrev (u) : |h u-g u| ≤ 2*S := by rw [abs_sub_comm]; exact hdiff u
  have hup := PhaseEssSup.value_le_ae (f₀ := fun p => f₀ p-k₀ p) (a := I) hT hL ht (hgm.sub hhm) hdiff
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T)
    (hinit.mono (fun p hp => (le_abs_self _).trans hp))
    (hsource.mono (fun u hu _ => (le_abs_self _).trans hu))
  have hlo := PhaseEssSup.value_le_ae (f₀ := fun p => k₀ p-f₀ p) (a := I) hT hL ht (hhm.sub hgm) hrev
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T)
    (hinit.mono (fun p hp => (abs_sub_le_iff.mp hp).2))
    (hsource.mono (fun u hu _ => (abs_sub_le_iff.mp hu).2))
  have hb : Real.exp (-L*t)*I+(∫ r in 0..t, Real.exp (-L*(t-r))*D) ≤ I+T*D := by
    have h := value_bounds hT hL hI hD JetBarrier.flight
      (fun _ => ⟨hI,le_rfl⟩) (fun _ => ⟨hD,le_rfl⟩) (t,(0 : JetPrototype.Phase))
    simpa only [value,GaussianLocal.time_eq ht] using h.2
  filter_upwards [hup,hlo] with p hp hq
  change value T L JetBarrier.flight (fun p => f₀ p-k₀ p) (fun u => g u-h u) (t,p) ≤ _ at hp
  change value T L JetBarrier.flight (fun p => k₀ p-f₀ p) (fun u => h u-g u) (t,p) ≤ _ at hq
  rw [← value_sub hT hL hgm hhm hg hh f₀ k₀ (t,p)] at hp
  rw [← value_sub hT hL hhm hgm hh hg k₀ f₀ (t,p)] at hq
  exact abs_sub_le_iff.mpr ⟨hp.trans hb,hq.trans hb⟩

theorem value_difference_initial_ae_all {T L S D I : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-k₀ p| ≤ I)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, |g u-h u| ≤ D) (t : ℝ) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |value T L JetBarrier.flight f₀ g (t,p)-value T L JetBarrier.flight k₀ h (t,p)| ≤ I+T*D := by
  filter_upwards [value_difference_initial_ae hT hL hD hI (time_bounds hT t)
    hinit hgm hhm hg hh hsource] with p hp
  rw [value_time_clamp hT L f₀ g (t,p),value_time_clamp hT L k₀ h (t,p)] at hp
  exact hp

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Order of the characteristic integral for almost-everywhere data -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

theorem value_mono_ae {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ ≤ᵐ[phaseVolume] k₀) (hsource : g ≤ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S) (t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) ≤ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hr := ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs)
  filter_upwards [hi,hr] with p hip hrp
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  apply intervalIntegral.integral_mono_ae (PositiveIntegral.time_bounds hT t).1
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p))
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hhm hh (t,p))
  filter_upwards [hrp] with r hrr
  exact mul_le_mul_of_nonneg_left hrr (Real.exp_pos _).le

end BoltzmannNonuniqueness.FlightMeasure

end

end

section

/-! # Absolute values and finite family differences under the positive integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_abs_le (T L : ℝ) (f₀ : JetPrototype.Phase → ℝ)
    (g : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    |value T L JetBarrier.flight f₀ g u| ≤
      value T L JetBarrier.flight (fun p => |f₀ p|) (fun z => |g z|) u := by
  unfold value
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  · apply (intervalIntegral.abs_integral_le_integral_abs
      (show 0 ≤ time T u.1 from le_max_left _ _)).trans_eq
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]

theorem finite_difference_le {I : Type*} {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (s : Finset I) (f₀ k₀ : I → JetPrototype.Phase → ℝ)
    (g h : I → ℝ × JetPrototype.Phase → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hhm : ∀ i ∈ s, Measurable (h i))
    (hg : ∀ i ∈ s, ∀ u, |g i u| ≤ S) (hh : ∀ i ∈ s, ∀ u, |h i u| ≤ S)
    (u : ℝ × JetPrototype.Phase) :
    (∑ i ∈ s, |value T L JetBarrier.flight (f₀ i) (g i) u-
      value T L JetBarrier.flight (k₀ i) (h i) u|) ≤
      value T L JetBarrier.flight (fun p => ∑ i ∈ s, |f₀ i p-k₀ i p|)
        (fun z => ∑ i ∈ s, |g i z-h i z|) u := by
  calc
    _ ≤ ∑ i ∈ s, value T L JetBarrier.flight
        (fun p => |f₀ i p-k₀ i p|) (fun z => |g i z-h i z|) u := by
      apply Finset.sum_le_sum
      intro i hi
      rw [value_sub hT hL (hgm i hi) (hhm i hi) (hg i hi) (hh i hi)]
      exact value_abs_le T L _ _ u
    _ = _ := value_finsetSum hT hL GaussianLocal.measurable_flight s _ _
      (fun i hi => (hgm i hi |>.sub (hhm i hi)).abs)
      (S := 2*S) (fun i hi z => by
        rw [abs_abs]
        exact (abs_sub _ _).trans (by linarith [hg i hi z,hh i hi z])) u

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # A.e. estimates for finite sums of absolute characteristic differences -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_le_constant_ae {T L S D I t : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hI : 0 ≤ I) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g : ℝ × JetPrototype.Phase → ℝ}
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ I)
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume, g u ≤ D) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, value T L JetBarrier.flight f₀ g (t,p) ≤ I+T*D := by
  have hp := PhaseEssSup.value_le_ae hT hL ht hgm hg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 T) hinit
    (hsource.mono (fun u hu _ => hu))
  have hb : Real.exp (-L*t)*I+(∫ r in 0..t, Real.exp (-L*(t-r))*D) ≤ I+T*D := by
    have h := value_bounds hT hL hI hD JetBarrier.flight
      (fun _ => ⟨hI,le_rfl⟩) (fun _ => ⟨hD,le_rfl⟩) (t,(0 : JetPrototype.Phase))
    simpa only [value,GaussianLocal.time_eq ht] using h.2
  exact hp.mono (fun p hp => hp.trans hb)

theorem finite_difference_ae {I : Type*} {T L S D A : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (s : Finset I) (f₀ k₀ : I → JetPrototype.Phase → ℝ)
    (g h : I → ℝ × JetPrototype.Phase → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hhm : ∀ i ∈ s, Measurable (h i))
    (hg : ∀ i ∈ s, ∀ u, |g i u| ≤ S) (hh : ∀ i ∈ s, ∀ u, |h i u| ≤ S)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, |f₀ i p-k₀ i p|) ≤ A)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      (∑ i ∈ s, |g i u-h i u|) ≤ D) (t : ℝ) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∑ i ∈ s, |value T L JetBarrier.flight (f₀ i) (g i) (t,p)-
        value T L JetBarrier.flight (k₀ i) (h i) (t,p)|) ≤ A+T*D := by
  let G (u : ℝ × JetPrototype.Phase) := ∑ i ∈ s, |g i u-h i u|
  have hGm : Measurable G := Finset.measurable_sum s (fun i hi => (hgm i hi |>.sub (hhm i hi)).abs)
  have hGb (u) : |G u| ≤ (s.card:ℝ)*(2*S) := by
    change |(∑ i ∈ s, |g i u-h i u|)| ≤ _
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    calc
      _ ≤ ∑ i ∈ s, 2*S := Finset.sum_le_sum (fun i hi => (abs_sub _ _).trans
        (by linarith [hg i hi u,hh i hi u]))
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  have hv := value_le_constant_ae hT hL hD hA (time_bounds hT t) hinit hGm hGb hsource
  filter_upwards [hv] with p hp
  have hval := finite_difference_le hT hL s f₀ k₀ g h hgm hhm hg hh (t,p)
  have he := value_time_clamp hT L (fun p => ∑ i ∈ s, |f₀ i p-k₀ i p|) G (t,p)
  exact hval.trans (he.symm.trans_le hp)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Restricting and translating the damped mild integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_eq_at_time {T U t : ℝ} (ht : t ∈ Icc 0 T) (hu : t ≤ U)
    (L : ℝ) (f₀ : JetPrototype.Phase → ℝ) {g h : ℝ × JetPrototype.Phase → ℝ}
    (hgh : ∀ r ∈ Icc 0 t, ∀ p, g (r,p) = h (r,p)) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,p) = value U L JetBarrier.flight f₀ h (t,p) := by
  unfold value
  rw [GaussianLocal.time_eq ht,GaussianLocal.time_eq ⟨ht.1,hu⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  dsimp only
  rw [hgh r hr]

theorem shifted_value {U s t : ℝ} (ht : t-s ∈ Icc 0 U) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value U L JetBarrier.flight f₀ g (t-s,p) =
      Real.exp (-L*(t-s))*f₀ (JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p) := by
  unfold value
  rw [GaussianLocal.time_eq ht]
  have he : -(t-s) = s-t := by ring
  rw [he]
  congr 1
  have hi := intervalIntegral.integral_comp_add_right
    (fun r => Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p)) s
    (a := 0) (b := t-s)
  rw [zero_add,sub_add_cancel] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  have h₁ : t-(r+s) = t-s-r := by ring
  have h₂ : r+s-s = r := by ring
  have h₃ : r+s-t = r-(t-s) := by ring
  rw [h₁,h₂,h₃]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
