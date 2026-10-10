import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalScaling
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundary

namespace OAI

/-! The logarithmic exterior equation transforms into the actual radial stationary equation. -/

namespace DefocusingNLS

noncomputable def radialPhysicalJet (ν : ℂ) (Z : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  (radialPhysicalExterior ν Z r,radialPhysicalExteriorSlope ν Z r)

theorem radialPhysicalJet_hasDerivAt (k : ℕ) (hk : 0 < k) (b r : ℝ) (hr : 0 < r)
    (Z : ℝ → ℂ × ℂ)
    (hZ : HasDerivAt Z
      (radialExteriorODEField (-1/(k : ℂ)+2*Complex.I*(b : ℂ)) k (Real.log r) (Z (Real.log r))) (Real.log r)) :
    let ν := -1/(k : ℂ)+2*Complex.I*(b : ℂ)
    let W := radialPhysicalJet ν Z
    HasDerivAt W
      ((W r).2,-(11/r : ℝ)*(W r).2-
        Complex.I*((r/2 : ℝ)*(W r).2+(1/(2*(k : ℝ)) : ℝ)*(W r).1)-
        (b : ℂ)*(W r).1+oddPowerNonlinearity k (W r).1) r := by
  intro ν W
  let A := Complex.exp (ν*(Real.log r : ℂ))
  let f := (Z (Real.log r)).1
  let g := (Z (Real.log r)).2
  let g' := -(2*ν+10+Complex.I*(Real.exp (2*Real.log r)/2 : ℝ))*g-
    ν*(ν+10)*f+oddPowerNonlinearity k f
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hlog := Real.hasDerivAt_log hr.ne'
  have hA := (hlog.ofReal_comp.const_mul ν).cexp
  have hF := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (Real.log r) hZ
  have hG := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (Real.log r) hZ
  change HasDerivAt (fun t => (Z t).1) g (Real.log r) at hF
  change HasDerivAt (fun t => (Z t).2) g' (Real.log r) at hG
  have hfr : HasDerivAt (fun t => (Z (Real.log t)).1) (g/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm] using!
      hF.scomp r hlog
  have hgr : HasDerivAt (fun t => (Z (Real.log t)).2) (g'/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm] using!
      hG.scomp r hlog
  have hfac : HasDerivAt (fun t : ℝ => Complex.exp (ν*(Real.log t : ℂ))/(t : ℂ))
      (A*(ν-1)/(r : ℂ)^2) r := by
    convert hA.div (hasDerivAt_id r).ofReal_comp hrC using 1
    · rfl
    · dsimp only [A,id_eq]
      push_cast
      field_simp
  have hbr := (hfr.const_mul ν).add hgr
  have hout := (radialPhysicalExterior_hasDerivAt ν k Z r hr hZ).prodMk (hfac.mul hbr)
  change HasDerivAt W _ r at hout
  apply hout.congr_deriv
  apply Prod.ext
  · rfl
  · have hN : oddPowerNonlinearity k (A*f)=A/(r : ℂ)^2*oddPowerNonlinearity k f :=
      radialPhysicalFactor_oddPower k hk b r hr f
    have he : Real.exp (2*Real.log r)=r^2 := by
      rw [two_mul,Real.exp_add,Real.exp_log hr]
      ring
    dsimp only [W,radialPhysicalJet,radialPhysicalExterior,radialPhysicalExteriorSlope]
    change A*(ν-1)/(r : ℂ)^2*(ν*f+g)+(A/(r : ℂ))*(ν*(g/(r : ℂ))+g'/(r : ℂ))=
      -(11/r : ℝ)*(A/(r : ℂ)*(ν*f+g))-
        Complex.I*((r/2 : ℝ)*(A/(r : ℂ)*(ν*f+g))+(1/(2*(k : ℝ)) : ℝ)*(A*f))-
        (b : ℂ)*(A*f)+oddPowerNonlinearity k (A*f)
    rw [hN]
    dsimp only [g']
    rw [he]
    dsimp only [ν]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

end DefocusingNLS

end OAI
