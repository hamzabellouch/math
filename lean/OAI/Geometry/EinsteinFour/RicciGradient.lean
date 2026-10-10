import OAI.Geometry.EinsteinFour.GradientMixedPairing

namespace OAI

/-! The algebraic part of the Ricci-commuted gradient equation, retaining
an arbitrary Bianchi test tensor. The raw operator is the sum of the
differentiated Weyl equation, Ricci curvature, and bundle curvature. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

def mixedGradient (s : Fin 3) (Z : Tensor) : RawGradient := fun a b =>
  quaternion s (matrixRotation s Z a b)

theorem mixedGradient_pairing (s : Fin 3) (Z W : Tensor) :
    rawPairing (mixedGradient s Z) W.matrix = mixedCouplingPairing s Z W := by
  rw [rawPairing_vectors]
  rfl

theorem sum_mixedGradient (Z : Tensor) (hb : Z.bianchi) :
    (∑ s, mixedGradient s Z) = (-4 : ℝ) • Z.matrix := by
  funext a b
  change (∑ s, quaternion s (matrixRotation s Z a b)) = (-4 : ℝ) • Z.matrix a b
  exact gradientCoupling_eq Z hb a b

/-- This is the uncompressed right side after applying Ricci commutation
and divergence freedom, with Ricci normalized to `3g`. Its coefficients
are `6 + 3`, `-12`, and the full bundle action `-(1+t_s) I_s Σ_s`. -/
def ricciGradient (t : Fin 3 → ℝ) (Z : Tensor) : RawGradient :=
  (9 : ℝ) • Z.matrix - (12 : ℝ) • rawMatrixCurvature t Z -
    ∑ s, (1 + t s) • mixedGradient s Z

/-- The coefficient `20` follows from bilinear compression of the actual
bundle action. No compressed differential equation is assumed. -/
theorem ricciGradient_pairing (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi)
    (hw : W.traceFree) (hbw : W.bianchi) :
    rawPairing (ricciGradient t Z) W.matrix =
      13 * rawPairing Z.matrix W.matrix -
        20 * rawPairing (rawMatrixCurvature t Z) W.matrix := by
  have hc : (∑ s, mixedCouplingPairing s Z W) = -4 * rawPairing Z.matrix W.matrix := by
    simp_rw [← mixedGradient_pairing]
    rw [← rawPairing_sum_left (fun s => mixedGradient s Z),
      sum_mixedGradient Z hbz, rawPairing_smul_left]
  have ht' := weighted_mixed_rawMatrixCurvature t ht Z W hz hbz hw hbw
  simp only [ricciGradient, rawPairing_sub_left, rawPairing_smul_left,
    rawPairing_sum_left, mixedGradient_pairing, add_mul,
    one_mul, Finset.sum_add_distrib]
  rw [hc, ht']
  ring

/-- The bilinear identity is precisely the concrete orthogonal compression
used by the squared-gradient and matrix-slot Green formulas. -/
theorem ricciGradient_compressed_pairing (S : Shape) (v : ℝ) (p k l : Vec)
    (W : Tensor) (hw : W.traceFree) (hbw : W.bianchi) :
    rawPairing (ricciGradient (fun s => v * S.s s) (parameters S p k l)) W.matrix =
      rawPairing ((13 : ℝ) • (parameters S p k l).matrix -
        (20 : ℝ) • (curvatureAction S v p k l).matrix) W.matrix := by
  have ht : ∑ s, v * S.s s = 0 := by rw [← Finset.mul_sum, S.trace, mul_zero]
  rw [ricciGradient_pairing _ ht _ W (parameters_traceFree S p k l)
    (parameters_bianchi S p k l) hw hbw, rawPairing_sub_left,
    rawPairing_smul_left, rawPairing_smul_left,
    rawMatrixCurvature_pairing _ _ W hw, diagonalGradientPairing_curvatureBilinear]
  simp only [tensor_pairing_eq_raw]
  rw [curvatureAction_compression S v p k l W hw hbw,
    matrixCurvatureTensor_pairing S v _ W hw]

end
end PositiveEinsteinFour.Bianchi

end OAI
