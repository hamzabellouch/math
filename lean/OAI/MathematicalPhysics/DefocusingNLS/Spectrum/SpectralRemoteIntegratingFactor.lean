import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralIntegralGronwall
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteTerminal

namespace OAI

/-! The scalar integrating factor for an incoming coordinate. Only the real
part of the coefficient enters its norm, so the large imaginary root costs
no power in this estimate. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralRemoteIntegratingFactor (T : ℝ) (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(∫ u in T..t, b u))

theorem spectralRemoteIntegratingFactor_base (T : ℝ) (b : ℝ → ℂ) :
    spectralRemoteIntegratingFactor T b T = 1 := by
  simp [spectralRemoteIntegratingFactor]

theorem spectralRemoteIntegratingFactor_deriv (L T t : ℝ) (hLT : L < T) (ht : T ≤ t)
    (b : ℝ → ℂ) (hb : ContinuousOn b (Ioi L)) :
    HasDerivAt (spectralRemoteIntegratingFactor T b)
      (-b t*spectralRemoteIntegratingFactor T b t) t := by
  have htt : t ∈ Ioi L := lt_of_lt_of_le hLT ht
  have hi : IntervalIntegrable b volume T t :=
    (hb.mono (fun u hu => lt_of_lt_of_le hLT hu.1)).intervalIntegrable_of_Icc ht
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    (hb.stronglyMeasurableAtFilter isOpen_Ioi t htt)
    (hb.continuousAt (Ioi_mem_nhds htt))
  convert hd.neg.cexp using 1
  · rfl
  · exact mul_comm _ _

theorem spectralRemoteIntegratingFactor_equation (L T t : ℝ) (hLT : L < T) (ht : T ≤ t)
    (b y f : ℝ → ℂ) (hb : ContinuousOn b (Ioi L))
    (hy : HasDerivAt y (b t*y t+f t) t) :
    HasDerivAt (fun u => spectralRemoteIntegratingFactor T b u*y u)
      (spectralRemoteIntegratingFactor T b t*f t) t := by
  apply ((spectralRemoteIntegratingFactor_deriv L T t hLT ht b hb).mul hy).congr_deriv
  ring

theorem spectralRemoteIntegratingFactor_bound (L T t C : ℝ) (hLT : L < T) (ht : T ≤ t)
    (b : ℝ → ℂ) (hb : ContinuousOn b (Ioi L))
    (hbound : ∀ u ∈ Ioi L, |(b u).re| ≤ C) :
    ‖spectralRemoteIntegratingFactor T b t‖ ≤ Real.exp (C*(t-T)) := by
  have hi : IntervalIntegrable b volume T t :=
    (hb.mono (fun u hu => lt_of_lt_of_le hLT hu.1)).intervalIntegrable_of_Icc ht
  have hlower : -C*(t-T) ≤ (∫ u in T..t, b u).re := by
    have hre : (∫ u in T..t, b u).re = ∫ u in T..t, (b u).re :=
      (intervalIntegral.intervalIntegral_re hi).symm
    rw [hre]
    have hirc : IntervalIntegrable (fun u => (b u).re) volume T t :=
      (Complex.continuous_re.comp_continuousOn
        (hb.mono (fun u hu => lt_of_lt_of_le hLT hu.1))).intervalIntegrable_of_Icc ht
    have hh := intervalIntegral.integral_mono_on ht intervalIntegrable_const hirc
      (fun u hu => (abs_le.mp (hbound u (lt_of_lt_of_le hLT hu.1))).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, neg_mul, mul_comm] using hh
  rw [spectralRemoteIntegratingFactor, Complex.norm_exp, Complex.neg_re]
  exact Real.exp_le_exp.mpr (by linarith)

end DefocusingNLS

end OAI
