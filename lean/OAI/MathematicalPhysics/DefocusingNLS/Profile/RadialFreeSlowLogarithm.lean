import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeRiccati
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowJet

namespace OAI

/-! The slow outgoing jet gives the actual physical logarithmic derivative. -/

namespace DefocusingNLS

theorem normalizedSlowFirst_cancel (q : ℂ) (x : ℂ) (hx : x ≠ 0) :
    -2*q*normalizedSlowSolution q 6 x+2*x*normalizedSlowFirst q 6 x=
      2*x*x^q*deriv (regularizedSlowSolution q 6) x := by
  have he : x^(q-1)*x=x^q := by
    calc
      _ = x^(q-1)*x^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = x^((q-1)+1) := (Complex.cpow_add _ _ hx).symm
      _ = _ := by congr 1; ring
  unfold normalizedSlowSolution normalizedSlowFirst
  calc
    _ = 2*q*regularizedSlowSolution q 6 x*(x^(q-1)*x-x^q)+
        2*x*x^q*deriv (regularizedSlowSolution q 6) x := by ring
    _ = _ := by rw [he,sub_self,mul_zero,zero_add]

theorem radialFreeSlow_physical_log (b r : ℝ) (hr : 0 < r) (m : ℂ)
    (hv : (radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)).1 ≠ 0) :
    ((2*Complex.I*(b : ℂ))*(radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)).1+
      (radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)).2)/
        ((r : ℂ)*(radialFreeSlowJet (-Complex.I*(b : ℂ)) m (Real.log r)).1)=
      radialFreeLog b r := by
  let q := -Complex.I*(b : ℂ)
  let x := freeRadialArgument r
  have hx : x ≠ 0 := Complex.slitPlane_ne_zero (freeRadialArgument_mem_slit hr)
  have he : Real.exp (2*Real.log r)=r^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hr]
    ring
  have harg : radialFreeSlowArgument (Real.log r)=x := by
    simp only [radialFreeSlowArgument,x,freeRadialArgument,he]
  change m*normalizedSlowSolution q 6 (radialFreeSlowArgument (Real.log r)) ≠ 0 at hv
  rw [harg] at hv
  have hm : m ≠ 0 := (mul_ne_zero_iff.mp hv).1
  have hH : regularizedSlowSolution q 6 x ≠ 0 :=
    (mul_ne_zero_iff.mp (show x^q*regularizedSlowSolution q 6 x ≠ 0 from
      (mul_ne_zero_iff.mp hv).2)).2
  have hp : x^q ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).2).1
  have hnum : (2*Complex.I*(b : ℂ))*(m*normalizedSlowSolution q 6 x)+
      m*(2*x*normalizedSlowFirst q 6 x)=
      m*(2*x*x^q*deriv (regularizedSlowSolution q 6) x) := by
    calc
      _ = m*(-2*q*normalizedSlowSolution q 6 x+2*x*normalizedSlowFirst q 6 x) := by
        dsimp [q]; ring
      _ = _ := by rw [normalizedSlowFirst_cancel q x hx]
  have htan : 2*x=(r : ℂ)*freeRadialTangent r := by
    dsimp [x,freeRadialArgument,freeRadialTangent]
    push_cast
    ring
  change ((2*Complex.I*(b : ℂ))*radialFreeSlowValue q m (Real.log r)+
    radialFreeSlowVelocity q m (Real.log r))/((r : ℂ)*radialFreeSlowValue q m (Real.log r))=_
  unfold radialFreeSlowValue radialFreeSlowVelocity
  rw [harg,hnum]
  rw [radialFreeLog,(radialFreeRaw_hasDerivAt b r hr).deriv]
  change (m*(2*x*x^q*deriv (regularizedSlowSolution q 6) x))/
      ((r : ℂ)*(m*(x^q*regularizedSlowSolution q 6 x)))=
    freeRadialTangent r*deriv (regularizedSlowSolution q 6) x/regularizedSlowSolution q 6 x
  rw [htan]
  field_simp [hm,hp,hH,Complex.ofReal_ne_zero.mpr hr.ne']

end DefocusingNLS

end OAI
