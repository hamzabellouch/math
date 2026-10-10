import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingLimit

namespace OAI

/-! Actual physical inner and outer boundary values and derivatives agree. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialPhysicalExterior (ν : ℂ) (Z : ℝ → ℂ × ℂ) (r : ℝ) : ℂ :=
  Complex.exp (ν*(Real.log r : ℂ))*(Z (Real.log r)).1

noncomputable def radialPhysicalExteriorSlope (ν : ℂ) (Z : ℝ → ℂ × ℂ) (r : ℝ) : ℂ :=
  Complex.exp (ν*(Real.log r : ℂ))/(r : ℂ)*(ν*(Z (Real.log r)).1+(Z (Real.log r)).2)

theorem radialPhysicalExterior_hasDerivAt (ν : ℂ) (n : ℕ) (Z : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : 0 < r)
    (hZ : HasDerivAt Z (radialExteriorODEField ν n (Real.log r) (Z (Real.log r))) (Real.log r)) :
    HasDerivAt (radialPhysicalExterior ν Z) (radialPhysicalExteriorSlope ν Z r) r := by
  have hlog := Real.hasDerivAt_log hr.ne'
  have he := (hlog.ofReal_comp.const_mul ν).cexp
  have hz₀ := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (Real.log r) hZ
  change HasDerivAt (fun t => (Z t).1) (Z (Real.log r)).2 (Real.log r) at hz₀
  have hz : HasDerivAt (fun t => (Z (Real.log t)).1)
      ((Z (Real.log r)).2*r⁻¹) r := by
    simpa only [Function.comp_def,Complex.real_smul,mul_comm] using! hz₀.scomp r hlog
  convert he.mul hz using 1
  · rfl
  · simp only [radialPhysicalExteriorSlope]
    push_cast
    ring

noncomputable def radialShootingExteriorProfile (n : ℕ) (z : ProfileMatchingBall) : ℝ → ℂ :=
  radialPhysicalExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
    (radialExteriorCanonical (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))

theorem radialShootingExteriorProfile_ne_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : innerBoundaryRadius ≤ r) : radialShootingExteriorProfile n z r ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  exact ((radialExteriorCanonical_spec hX).2.2 (Real.log r)
    (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr)).1

theorem radialShootingExteriorProfile_differentiableAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : innerBoundaryRadius ≤ r) :
    DifferentiableAt ℝ (radialShootingExteriorProfile n z) r := by
  exact (radialPhysicalExterior_hasDerivAt _ _ _ r (by linarith [innerBoundaryRadius_bounds.1])
    ((radialExteriorCanonical_spec hX).2.2 (Real.log r)
      (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr)).2).differentiableAt

theorem radialMatchingMap_zero_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    radialShootingExteriorProfile n z innerBoundaryRadius=
      radialShootingInnerComplex n (profileMatchingParameter z) innerBoundaryRadius ∧
    deriv (radialShootingExteriorProfile n z) innerBoundaryRadius=
      deriv (radialShootingInnerComplex n (profileMatchingParameter z)) innerBoundaryRadius := by
  let I := radialShootingInnerBoundary n (profileMatchingParameter z)
  let E := radialShootingExteriorJet (n+radialInnerShootingThreshold) z
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let A := Complex.exp (ν*(Real.log innerBoundaryRadius : ℂ))
  have hI : I.1 ≠ 0 := radialShootingInnerBoundary_ne_zero n (profileMatchingParameter z)
  have hE : E.1 ≠ 0 :=
    ((radialExteriorCanonical_spec hX).2.2 (Real.log innerBoundaryRadius) le_rfl).1
  have hB : (innerBoundaryRadius : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith [innerBoundaryRadius_bounds.1])
  have hA : A ≠ 0 := Complex.exp_ne_zero _
  have hv := congrArg Prod.fst hz
  have hd := congrArg Prod.snd hz
  change 100*(Complex.exp (radialMatchingNu z _*(Real.log innerBoundaryRadius : ℂ))*E.1-I.1)=0 at hv
  rw [radialMatchingNu_eq] at hv
  change 100*(A*E.1-I.1)=0 at hv
  have hv' : A*E.1=I.1 := sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left (by norm_num))
  change (I.2/I.1-(radialMatchingNu z _*E.1+E.2)/((innerBoundaryRadius : ℂ)*E.1))/
    radialFreeMatchingFactor (profileMatchingParameter z)=0 at hd
  rw [radialMatchingNu_eq] at hd
  have hd' : I.2/I.1=(ν*E.1+E.2)/((innerBoundaryRadius : ℂ)*E.1) :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp hd).resolve_right (radialFreeMatchingFactor_ne_zero _))
  have hratio : (A/(innerBoundaryRadius : ℂ)*(ν*E.1+E.2))/(A*E.1)=
      (ν*E.1+E.2)/((innerBoundaryRadius : ℂ)*E.1) := by
    field_simp [hA,hB,hE]
  rw [← hratio,hv'] at hd'
  have hd'' : A/(innerBoundaryRadius : ℂ)*(ν*E.1+E.2)=I.2 :=
    (mul_right_cancel₀ (inv_ne_zero hI) hd').symm
  have hder := (radialPhysicalExterior_hasDerivAt ν (n+radialInnerShootingThreshold) _
    innerBoundaryRadius (by linarith [innerBoundaryRadius_bounds.1])
      ((radialExteriorCanonical_spec hX).2.2 (Real.log innerBoundaryRadius) le_rfl).2).deriv
  exact ⟨hv',hder.trans hd''⟩

theorem exists_radial_inner_outer_boundary_match :
    ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialShootingExteriorProfile n z innerBoundaryRadius=
        radialShootingInnerComplex n (profileMatchingParameter z) innerBoundaryRadius ∧
      deriv (radialShootingExteriorProfile n z) innerBoundaryRadius=
        deriv (radialShootingInnerComplex n (profileMatchingParameter z)) innerBoundaryRadius := by
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [exists_radialMatchingMap_zero,hs.eventually radialShootingExterior_exists] with n hn hX
  obtain ⟨z,hz⟩ := hn
  exact ⟨z,hX z,radialMatchingMap_zero_boundary n z (hX z) hz⟩

end DefocusingNLS

end OAI
