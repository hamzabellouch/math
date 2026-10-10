import OAI.Probability.InvariantIsing.Haar.HaarHeatContinuity
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMinimum

namespace OAI

/-! Positivity of the actual finite polynomial heat flow, by compact comparison. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped BigOperators
namespace InvariantIsing

theorem haarPolynomialHeat_nonneg {N d : ℕ} (p : haarPolynomialSpace N d)
    (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    0 ≤ haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U := by
  let q (s : ℝ) : MatrixPolynomial N := Real.exp (-s) •
    ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
  let Wt (z : ℝ × SpecialOrthogonal N) :=
    haarPolynomialValue (haarPolynomialLaplacian N (q z.1)) z.2-
      haarPolynomialValue (q z.1) z.2
  have hq (s : ℝ) (V : SpecialOrthogonal N) : haarPolynomialValue (q s) V =
      Real.exp (-s)*haarPolynomialValue
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (Real.exp (-s) • _) = _
    rw [map_smul]
    rfl
  have hL (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V =
      Real.exp (-s)*haarPolynomialValue (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (haarPolynomialLaplacian N (Real.exp (-s) • _)) = _
    rw [map_smul,map_smul,smul_eq_mul]
    rfl
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (q z.1) z.2) := by
    simp_rw [hq]
    exact (Real.continuous_exp.comp continuous_fst.neg).mul (continuous_haarPolynomialHeat_value p)
  have hi : ∀ V : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (q 0) V := by
    intro V
    simpa only [hq,neg_zero,Real.exp_zero,one_mul,haarPolynomialHeat_zero] using hp V
  have hd (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => haarPolynomialValue (q r) V) (Wt (s,V)) s := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := by
      convert ((hasDerivAt_id s).fun_neg).exp using 1
      all_goals simp only [id_eq,mul_neg,mul_one]
    have hv := haarPolynomialHeat_hasDerivAt p (V : Matrix (Fin N) (Fin N) ℝ) s
    convert he.mul hv using 1
    · funext r
      exact hq r V
    · change haarPolynomialValue (haarPolynomialLaplacian N (q s)) V-
        haarPolynomialValue (q s) V = _
      rw [hL,hq]
      simp only [haarPolynomialValue]
      ring
  have hz := haarPolynomial_parabolic_nonneg ht q Wt hc.continuousOn hi hd
    (fun _ _ _ => le_rfl) t ⟨ht,le_rfl⟩ U
  rw [hq] at hz
  exact nonneg_of_mul_nonneg_right hz (Real.exp_pos (-t))

end InvariantIsing

end

end OAI
