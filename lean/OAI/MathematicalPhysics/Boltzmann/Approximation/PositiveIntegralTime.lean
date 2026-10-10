import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Comparison for the damped scalar integral inequality -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveScalarComparison

theorem le_supersolution {T L K a : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    {z u : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hzc : ContinuousOn z (Icc 0 T)) (huc : ContinuousOn u (Icc 0 T))
    (hzi : IntervalIntegrable (fun r => G r (z r)) volume 0 T)
    (hui : IntervalIntegrable (fun r => G r (u r)) volume 0 T)
    (hz : ∀ t ∈ Icc 0 T, z t ≤ Real.exp (-L*t)*a+
      ∫ r in 0..t, Real.exp (-L*(t-r))*G r (z r))
    (hu : ∀ t ∈ Icc 0 T, Real.exp (-L*t)*a+
      ∫ r in 0..t, Real.exp (-L*(t-r))*G r (u r) ≤ u t)
    (hlip : ∀ r ∈ Icc 0 T, G r (z r)-G r (u r) ≤ K*max 0 (z r-u r)) :
    ∀ t ∈ Icc 0 T, z t ≤ u t := by
  let d (r : ℝ) := max 0 (z r-u r)
  have hdc : ContinuousOn d (Icc 0 T) :=
    (show Continuous (fun x : ℝ => max 0 x) from continuous_const.max continuous_id).comp_continuousOn
      (hzc.sub huc)
  have hdi : IntervalIntegrable d volume 0 T := hdc.intervalIntegrable_of_Icc hT
  have hn (r : ℝ) : 0 ≤ d r := le_max_left _ _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : d t ≤ K*ColdGronwall.primitive d t := by
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1,uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hzt := (hzi.mono_set hsub).continuousOn_mul
      (show ContinuousOn (fun r => Real.exp (-L*(t-r))) (uIcc 0 t) by fun_prop)
    have hut := (hui.mono_set hsub).continuousOn_mul
      (show ContinuousOn (fun r => Real.exp (-L*(t-r))) (uIcc 0 t) by fun_prop)
    have hdt := hdi.mono_set hsub
    have hdiff : z t-u t ≤ ∫ r in 0..t,
        Real.exp (-L*(t-r))*(G r (z r)-G r (u r)) := by
      have h₁ := hz t ht
      have h₂ := hu t ht
      rw [show (fun r => Real.exp (-L*(t-r))*(G r (z r)-G r (u r))) =
        (fun r => Real.exp (-L*(t-r))*G r (z r)-Real.exp (-L*(t-r))*G r (u r)) by
          funext r; ring, intervalIntegral.integral_sub hzt hut]
      linarith
    have hint : (∫ r in 0..t, Real.exp (-L*(t-r))*(G r (z r)-G r (u r))) ≤
        K*ColdGronwall.primitive d t := by
      rw [ColdGronwall.primitive,← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on ht.1
        ((hzi.sub hui).mono_set hsub |>.continuousOn_mul (by fun_prop)) (hdt.const_mul K)
      intro r hr
      have he : Real.exp (-L*(t-r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
      calc
        _ ≤ Real.exp (-L*(t-r))*(K*d r) :=
          mul_le_mul_of_nonneg_left (hlip r ⟨hr.1,hr.2.trans ht.2⟩) (Real.exp_pos _).le
        _ ≤ K*d r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (mul_nonneg hK (hn r))
    exact max_le (mul_nonneg hK (intervalIntegral.integral_nonneg_of_forall ht.1 hn)) (hdiff.trans hint)
  have hd0 := ColdGronwall.eq_zero_of_integral_bound hK hT hdi (fun r _ => hn r) hbound
  intro t ht
  have hd := hd0 t ht
  have h := le_max_right 0 (z t-u t)
  change z t-u t ≤ d t at h
  rw [hd] at h
  linarith

end BoltzmannNonuniqueness.PositiveScalarComparison

end

end

section

/-! # Restarting the mild equation at an intermediate time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem restart {T L S s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (f₀ : JetPrototype.Phase → ℝ) {g : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,p) =
      Real.exp (-L*(t-s)) * value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hti : time T t = t := GaussianLocal.time_eq ⟨ht0,ht⟩
  have hsi : time T s = s := GaussianLocal.time_eq ⟨hs,hst.trans ht⟩
  let a (r : ℝ) := Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)
  have hi : IntervalIntegrable a volume 0 t := by
    have h := damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
    simpa only [hti] using h
  have his : IntervalIntegrable a volume 0 s := by
    apply hi.mono_set
    rw [uIcc_of_le hs,uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl hst
  have hist : IntervalIntegrable a volume s t := by
    apply hi.mono_set
    rw [uIcc_of_le hst,uIcc_of_le ht0]
    exact Icc_subset_Icc hs le_rfl
  have hinit : Real.exp (-L*(t-s))*value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) =
      Real.exp (-L*t)*f₀ (JetBarrier.flight (-t) p) + ∫ r in 0..s,a r := by
    unfold value
    rw [hsi,mul_add,← intervalIntegral.integral_const_mul]
    congr 1
    · rw [JetFreeTransport.flight_add]
      have he : -s+(s-t) = -t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
    · apply intervalIntegral.integral_congr
      intro r _
      dsimp only [a]
      rw [JetFreeTransport.flight_add]
      have he : r-s+(s-t) = r-t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
  rw [hinit]
  change value T L JetBarrier.flight f₀ g (t,p) = _ + ∫ r in s..t,a r
  unfold value
  rw [hti,← intervalIntegral.integral_add_adjacent_intervals his hist]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Time regularity along the free paths without continuity of translations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem along_time_bound {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (_hS : 0 ≤ S) (_hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = value T L JetBarrier.flight f₀ g z) (p : JetPrototype.Phase) :
    |f (t,p)-f (s,JetBarrier.flight (s-t) p)| ≤ (L*R+S)*(t-s) := by
  have hr := restart hT hL hs hst ht f₀ hgm hg p
  rw [← hf (t,p),← hf (s,JetBarrier.flight (s-t) p)] at hr
  have he : Real.exp (-L*(t-s)) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hst))
  have hediff : |Real.exp (-L*(t-s))-1| ≤ L*(t-s) := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    have ha := Real.add_one_le_exp (-L*(t-s))
    linarith
  have hi : |∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| ≤ S*(t-s) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (C := S)
      (f := fun r => Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)) (by
        intro r hrt
        rw [uIoc_of_le hst] at hrt
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        have hx : Real.exp (-L*(t-r)) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hrt.2))
        exact (mul_le_mul hx (hg _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul S))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh
  have hsB := hfB (s,JetBarrier.flight (s-t) p)
  have hiB : |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p)| ≤ L*(t-s)*R := by
    rw [abs_mul]
    exact mul_le_mul hediff hsB (abs_nonneg _) (mul_nonneg hL (sub_nonneg.mpr hst))
  calc
    _ = |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p) +
        ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| := by
      rw [hr]
      congr 1
      ring
    _ ≤ L*(t-s)*R+S*(t-s) := (abs_add_le _ _).trans (add_le_add hiB hi)
    _ = _ := by ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
