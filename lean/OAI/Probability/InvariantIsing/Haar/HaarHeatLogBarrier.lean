import OAI.Probability.InvariantIsing.Haar.HaarLogBarrier
import OAI.Probability.InvariantIsing.Haar.HaarHeatOperator
import OAI.Probability.InvariantIsing.Haar.HaarHeatGammaDerivative

namespace OAI

/-! Time differentiation and continuity of the logarithmic gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarHeatLogBarrier {N d : ℕ} (p : haarPolynomialSpace N d) (C t : ℝ) : MatrixPolynomial N :=
  haarLogBarrier ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
    (C*Real.exp (-2*((N:ℝ)-2)*t))

lemma continuous_haarHeatLogBarrier {N d : ℕ} (p : haarPolynomialSpace N d) (C : ℝ) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (haarHeatLogBarrier p C z.1) z.2) := by
  have he (t : ℝ) (U : SpecialOrthogonal N) : haarPolynomialValue (haarHeatLogBarrier p C t) U =
      C*Real.exp (-2*((N:ℝ)-2)*t)*
        (haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)^2-
      haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U :=
    haarLogBarrier_eval _ _ _
  simp_rw [he]
  exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
    ((continuous_haarPolynomialHeat_value p).pow 2)).sub (continuous_haarPolynomialHeat_gamma p)

lemma haarHeatLogBarrier_hasDerivAt {N d : ℕ} (p : haarPolynomialSpace N d)
    (C t : ℝ) (U : SpecialOrthogonal N) :
    HasDerivAt (fun s => haarPolynomialValue (haarHeatLogBarrier p C s) U)
      (let q : MatrixPolynomial N := (haarPolynomialHeat N d t p : haarPolynomialSpace N d);
       let a := C*Real.exp (-2*((N:ℝ)-2)*t);
       -2*((N:ℝ)-2)*a*(haarPolynomialValue q U)^2+
        2*a*haarPolynomialValue q U*haarPolynomialValue (haarPolynomialLaplacian N q) U-
        2*haarPolynomialValue (haarPolynomialGamma q (haarPolynomialLaplacian N q)) U) t := by
  have ha : HasDerivAt (fun s => C*Real.exp (-2*((N:ℝ)-2)*s))
      (-2*((N:ℝ)-2)*(C*Real.exp (-2*((N:ℝ)-2)*t))) t := by
    convert (((hasDerivAt_id t).const_mul (-2*((N:ℝ)-2))).exp).const_mul C using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hu := haarPolynomialHeat_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) t
  have hg := haarPolynomialHeat_gamma_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) t
  convert (ha.mul (hu.pow 2)).sub hg using 1
  · funext s
    exact haarLogBarrier_eval _ _ _
  · dsimp only [haarPolynomialValue]
    simp only [Nat.cast_ofNat,Pi.pow_apply]
    ring

end InvariantIsing

end

end OAI
