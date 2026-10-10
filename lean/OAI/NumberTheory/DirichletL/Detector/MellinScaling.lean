import OAI.NumberTheory.DirichletL.Detector.RadialMellin
import OAI.NumberTheory.DirichletL.Detector.Physical

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open EisensteinSchwartzPoisson

def sourceMellinWeight (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w

lemma sourceMellinWeight_marked (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(x+z-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  ring

lemma sourceMellinWeight_rescaled (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hX : 0<X) (hY : 0<Y) (hQ : 0<Q) (x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z=
      (Q:ℂ)^(z-w-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold sourceMellinWeight
  rw [Complex.ofReal_div,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX.le hQ.le,Complex.div_cpow_ofReal_nonneg hY.le hQ.le,
    Complex.ofReal_cpow hQ.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg]
  have he : (Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))=(Q:ℂ)^(z-w-1) := by
    rw [←Complex.cpow_add _ _ hQc,←Complex.cpow_add _ _ hQc]
    congr 1
    push_cast
    ring
  calc
    _ = ((Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))) *
        ((X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
        Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w) := by ring_nf
    _ = _ := by rw [he]; simp only [div_eq_mul_inv]

lemma sourceMellinWeight_marked_factor (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (eta x w z : ℂ) :
    star eta*sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(z-1)*(star eta*(Q:ℂ)^x)*sourceMellinWeight W0 W1 X Y Z x w z := by
  rw [sourceMellinWeight_marked W0 W1 X Y Z Q hZ hQ x w z]
  rw [show x+z-1=(z-1)+x by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

end SevenEighths.ProbePhysical
end

end OAI
