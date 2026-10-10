import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDerivativeBounded
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalSlopeAsymptotic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! The actual translation mode, including its weighted top derivative and
nonvanishing at a positive radius. -/

open Filter Topology Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedEvenProfile_deriv_nonzero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ∃ r : ℝ, 0<r ∧ deriv (radialMatchedEvenProfile n z) r≠0 := by
  have ha : 0<radialShootingA n := by
    unfold radialShootingA
    exact one_div_pos.mpr (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))
  have hnu : radialShootingNu (n+radialInnerShootingThreshold) z≠0 := by
    intro he
    have hre := congrArg Complex.re he
    rw [radialShootingNu_physical] at hre
    simp only [Complex.add_re,Complex.neg_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hpos : 0<‖radialShootingNu (n+radialInnerShootingThreshold) z*radialShootingM z‖ :=
    norm_pos_iff.mpr (mul_ne_zero hnu (radialShootingM_ne_zero z))
  have hp := (radialMatchedProfile_scaled_deriv_tendsto n z hX hz).eventually
    (eventually_gt_nhds hpos)
  obtain ⟨r,hpr,hr⟩ := (hp.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨r,hr,?_⟩
  rw [(radialMatchedEvenProfile_eventuallyEq n z r hr).deriv_eq]
  intro he
  simp only [he,norm_zero,mul_zero] at hpr
  exact (lt_irrefl 0) hpr

private theorem iteratedDeriv_conjugate (f : ℝ → ℂ) (N : ℕ) :
    iteratedDeriv N (fun r => star (f r))=fun r => star (iteratedDeriv N f r) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iteratedDeriv_succ,ih,deriv.star',iteratedDeriv_succ]

noncomputable def radialMatchedTranslationMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ) (hN : 7≤N) :
    RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) 11 (1/2) := by
  let f := deriv (radialMatchedEvenProfile n z)
  have hf : ContDiff ℝ ∞ f := (radialMatchedEvenProfile_contDiff n z hX hz).deriv'
  have hg : ContDiff ℝ ∞ (fun r => star (f r)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hf
  have ht : IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N f r‖^2) (Ioi 0) := by
    simpa only [iteratedDeriv_succ'] using
      radialMatchedEvenProfile_top_integrable n z hX hz (N+1) (by omega)
  refine ⟨f,(fun r => star (f r)),hf.of_le (by norm_num),hg.of_le (by norm_num),
    radialMatched_translation_eigenpair n z hX hz,hf.contDiffOn,hg.contDiffOn,
    ht,?_,?_,?_⟩
  · simpa only [iteratedDeriv_conjugate,norm_star] using ht
  · obtain ⟨B,hB,hb⟩ := radialMatchedEvenProfile_iteratedDeriv_bounded n z hX hz 1
    refine ⟨B,hB,?_⟩
    intro r
    simpa only [Prod.norm_mk,norm_star,max_self,iteratedDeriv_one] using hb r
  · obtain ⟨r,hr,hn⟩ := radialMatchedEvenProfile_deriv_nonzero n z hX hz
    exact ⟨r,hr,Or.inl hn⟩

end DefocusingNLS

end OAI
