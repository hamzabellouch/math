import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularCoordinates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Returning a normalized circular spectral solution to the physical radial variable. -/

namespace DefocusingNLS

noncomputable def spectralPhysicalJet (ν : ℂ) (Y : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  (Complex.exp (ν*(Real.log r : ℂ))*(Y (Real.log r)).1,
   Complex.exp (ν*(Real.log r : ℂ))/(r : ℂ)*
     (ν*(Y (Real.log r)).1+(Y (Real.log r)).2))

theorem spectralPhysicalJet_hasDerivAt (h ν η : ℂ) (Y : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : 0 < r) (F : ℂ)
    (hY : HasDerivAt Y ((Y (Real.log r)).2,
      -(2*ν+10)*(Y (Real.log r)).2-(ν*(ν+10)-η)*(Y (Real.log r)).1-
        h*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).2+F) (Real.log r)) :
    HasDerivAt (spectralPhysicalJet ν Y)
      ((spectralPhysicalJet ν Y r).2,
        -(11/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*(spectralPhysicalJet ν Y r).2-
          (-h*Complex.I*ν/2-η/(r : ℂ)^2)*(spectralPhysicalJet ν Y r).1+
          Complex.exp (ν*(Real.log r : ℂ))/(r : ℂ)^2*F) r := by
  let A := Complex.exp (ν*(Real.log r : ℂ))
  let f := (Y (Real.log r)).1
  let g := (Y (Real.log r)).2
  let g' := -(2*ν+10)*g-(ν*(ν+10)-η)*f-
    h*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*g+F
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hlog := Real.hasDerivAt_log hr.ne'
  have hA := (hlog.ofReal_comp.const_mul ν).cexp
  have hf := hY.fst
  have hg := hY.snd
  change HasDerivAt (fun t => (Y t).1) g (Real.log r) at hf
  change HasDerivAt (fun t => (Y t).2) g' (Real.log r) at hg
  have hfr : HasDerivAt (fun t => (Y (Real.log t)).1) (g/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm] using
      hf.scomp r hlog
  have hgr : HasDerivAt (fun t => (Y (Real.log t)).2) (g'/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm] using
      hg.scomp r hlog
  have hfac : HasDerivAt (fun t : ℝ => Complex.exp (ν*(Real.log t : ℂ))/(t : ℂ))
      (A*(ν-1)/(r : ℂ)^2) r := by
    convert hA.div (hasDerivAt_id r).ofReal_comp hrC using 1
    · rfl
    · dsimp only [A,id_eq]
      push_cast
      field_simp
  have hvalue : HasDerivAt (fun t => Complex.exp (ν*(Real.log t : ℂ))*(Y (Real.log t)).1)
      (A/(r : ℂ)*(ν*f+g)) r := by
    apply (hA.mul hfr).congr_deriv
    change A*(ν*(r⁻¹ : ℝ))*f+A*(g/(r : ℂ)) = _
    push_cast
    field_simp
  have hh := hvalue.prodMk (hfac.mul ((hfr.const_mul ν).add hgr))
  apply hh.congr_deriv
  apply Prod.ext
  · rfl
  · have hexp : Real.exp (2*Real.log r)=r^2 := by
      rw [two_mul,Real.exp_add,Real.exp_log hr]
      ring
    change A*(ν-1)/(r : ℂ)^2*(ν*f+g)+(A/(r : ℂ))*(ν*(g/(r : ℂ))+g'/(r : ℂ)) = _
    dsimp only [spectralPhysicalJet]
    change _=-(11/(r : ℂ)+h*Complex.I*(r : ℂ)/2)*(A/(r : ℂ)*(ν*f+g))-
      (-h*Complex.I*ν/2-η/(r : ℂ)^2)*(A*f)+A/(r : ℂ)^2*F
    dsimp only [g']
    rw [hexp]
    push_cast
    field_simp
    ring

theorem spectralCircularNu_physical_coefficient (h : ℂ) (hh : h^2=1)
    (a b : ℝ) (lam : ℂ) :
    -h*Complex.I*spectralCircularNu h a b lam/2=(b : ℂ)+h*Complex.I*((a : ℂ)+lam) := by
  unfold spectralCircularNu
  ring_nf
  simp only [hh,Complex.I_sq]
  ring

end DefocusingNLS

end OAI
