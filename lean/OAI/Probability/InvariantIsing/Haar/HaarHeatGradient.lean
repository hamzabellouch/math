import OAI.Probability.InvariantIsing.Haar.HaarHeatGammaDerivative
import OAI.Probability.InvariantIsing.Haar.HaarHeatOperator
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialEvolution
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurvature
import OAI.Probability.InvariantIsing.Haar.HaarHeatConstants

namespace OAI

/-! Exponential squared-gradient decay for the actual orthogonal polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_gradient_bound {N d : ℕ}
    (p : haarPolynomialSpace N d) (C : ℝ)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    Real.exp (2*((N : ℝ)-2)*t)*haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤ C := by
  let u (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let g (s : ℝ) := haarPolynomialGamma (u s) (u s)
  let k : ℝ := 2*((N : ℝ)-2)
  let q (s : ℝ) : MatrixPolynomial N := C • 1-Real.exp (k*s) • g s
  let dq (s : ℝ) (V : SpecialOrthogonal N) :=
    -Real.exp (k*s)*(k*haarPolynomialValue (g s) V+
      2*haarPolynomialValue (haarPolynomialGamma (u s) (haarPolynomialLaplacian N (u s))) V)
  have heval (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (q s) V = C-Real.exp (k*s)*haarPolynomialValue (g s) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_) = _
    simp only [map_sub,map_smul,map_one,smul_eq_mul,mul_one,haarPolynomialValue]
  have hL (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V =
        -Real.exp (k*s)*haarPolynomialValue (haarPolynomialLaplacian N (g s)) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (haarPolynomialLaplacian N (C • 1-Real.exp (k*s) • g s)) = _
    rw [map_sub,map_smul,map_smul,haarPolynomialLaplacian_one,smul_zero,zero_sub,
      map_neg,map_smul,smul_eq_mul]
    simp only [haarPolynomialValue,neg_mul]
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (q z.1) z.2) := by
    simp_rw [heval]
    exact continuous_const.sub
      ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (continuous_haarPolynomialHeat_gamma p))
  have hi : ∀ V : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (q 0) V := by
    intro V
    rw [heval]
    simpa only [g,u,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,one_mul] using
      sub_nonneg.mpr (hC V)
  have hd (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => haarPolynomialValue (q r) V) (dq s V) s := by
    have he : HasDerivAt (fun r => Real.exp (k*r)) (k*Real.exp (k*s)) s := by
      convert ((hasDerivAt_id s).const_mul k).exp using 1
      all_goals simp only [id_eq]
      all_goals ring
    have hg := haarPolynomialHeat_gamma_hasDerivAt p (V : Matrix (Fin N) (Fin N) ℝ) s
    convert (hasDerivAt_const s C).sub (he.mul hg) using 1
    · funext r
      exact heval r V
    · dsimp only [dq,haarPolynomialValue,g,u]
      ring
  have hpde (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V ≤ dq s V := by
    have hb := matrixPolynomial_curvature (u s) (V : Matrix (Fin N) (Fin N) ℝ)
    have hh : k*haarPolynomialValue (g s) V+
        2*haarPolynomialValue (haarPolynomialGamma (u s) (haarPolynomialLaplacian N (u s))) V ≤
        haarPolynomialValue (haarPolynomialLaplacian N (g s)) V := by
      dsimp only [k,g,haarPolynomialValue]
      linarith
    rw [hL]
    dsimp only [dq]
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_pos (k*s)).le]
  have hz := haarPolynomial_evolution_nonneg ht q dq hc.continuousOn hi hd hpde t ⟨ht,le_rfl⟩ U
  rw [heval] at hz
  exact sub_nonneg.mp hz

end InvariantIsing

end

end OAI
