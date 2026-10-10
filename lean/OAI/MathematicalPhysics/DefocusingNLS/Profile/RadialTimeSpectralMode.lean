import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! The actual nonzero radial time-translation spectral mode. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedEuler_nonzero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ∃ r : ℝ, 0<r ∧ radialAffineEuler ((radialShootingA n : ℂ)-
      Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))
      (radialMatchedEvenProfile n z) r≠0 := by
  let c : ℂ := (radialShootingA n : ℂ)-
    Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)
  let T := radialAffineEuler c (radialMatchedEvenProfile n z)
  have hc : c≠0 := by
    intro he
    have hre := congrArg Complex.re he
    have ha : 0<radialShootingA n := by
      unfold radialShootingA
      exact one_div_pos.mpr (mul_pos (by norm_num)
        (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))
    simp only [c,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.zero_re] at hre
    exact ha.ne' hre
  have h0 : T 0≠0 := by
    simpa only [T,radialAffineEuler,Complex.ofReal_zero,zero_div,zero_mul,add_zero] using
      mul_ne_zero hc (radialMatchedEvenProfile_ne_zero n z hX 0)
  have hT := radialAffineEuler_contDiff c _ (radialMatchedEvenProfile_contDiff n z hX hz)
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), T r≠0 := hT.continuous.continuousAt.eventually_ne h0
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε/2,by linarith,hball ?_⟩
  simp only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
  rw [abs_of_pos (by linarith : 0<ε/2)]
  linarith

private theorem iteratedDeriv_conjugate (f : ℝ → ℂ) (N : ℕ) :
    iteratedDeriv N (fun r => star (f r))=fun r => star (iteratedDeriv N f r) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iteratedDeriv_succ,ih,deriv.star',iteratedDeriv_succ]

noncomputable def radialMatchedTimeMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ) (hN : 7≤N) :
    RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) 0 1 := by
  let c : ℂ := (radialShootingA n : ℂ)-
    Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)
  let T := radialAffineEuler c (radialMatchedEvenProfile n z)
  have hf : ContDiff ℝ ∞ T :=
    radialAffineEuler_contDiff c _ (radialMatchedEvenProfile_contDiff n z hX hz)
  have hg : ContDiff ℝ ∞ (fun r => star (T r)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hf
  have ht := radialMatchedEuler_top_integrable n z hX hz c N hN
  refine ⟨T,(fun r => star (T r)),hf.of_le (by norm_num),hg.of_le (by norm_num),
    radialMatched_time_eigenpair n z hX hz,hf.contDiffOn,hg.contDiffOn,ht,?_,?_,?_⟩
  · simpa only [iteratedDeriv_conjugate,norm_star] using ht
  · obtain ⟨B,hB,hb⟩ := radialMatchedEuler_bounded n z hX hz c
    refine ⟨B,hB,?_⟩
    intro r
    simpa only [Prod.norm_mk,norm_star,max_self] using hb r
  · obtain ⟨r,hr,hn⟩ := radialMatchedEuler_nonzero n z hX hz
    exact ⟨r,hr,Or.inl hn⟩

end DefocusingNLS

end OAI
