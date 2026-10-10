import OAI.Analysis.HyperbolicCones.ResolventFormula
import OAI.Analysis.HyperbolicCones.RankQuadratics

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem complex_symmetric_imaginary_posDef_isUnit {n : ℕ} (H : Mat n ℂ)
    (hH : H.IsSymm) (him : (H.map Complex.im).PosDef) : IsUnit H := by
  have hδ : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  apply isUnit_of_adjoint_difference_posDef H ((H.map Complex.im).map Complex.ofReal)
    (2 * Complex.I) hδ (posDef_complexify _ him)
  rw [complex_symmetric_imaginary H hH, smul_smul, mul_inv_cancel₀ hδ, one_smul]

theorem resolvent_schur_imaginary_lower_bound (X Z : Mat 4 ℝ) (hX : X.IsHermitian)
    (y : Fin 3 → ℝ) (a η : ℝ) (hη : 0 < η) :
    η • (1 : Mat 4 ℝ) ≤
      ((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat 4 ℂ) - Z.map Complex.ofReal -
        phi (fun i => (y i : ℂ))
          ((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat 4 ℂ) -
            X.map Complex.ofReal)⁻¹)).map Complex.im) := by
  let z : ℂ := (a : ℂ) + (η : ℂ) * Complex.I
  let R := (z • (1 : Mat 4 ℂ) - X.map Complex.ofReal)⁻¹
  have hneg : (-R.map Complex.im).PosSemidef :=
    (resolvent_negative_imaginary_posDef X hX a η hη).posSemidef
  have hsub (A B : Mat 4 ℂ) : (A - B).map Complex.im =
      A.map Complex.im - B.map Complex.im := by
    ext i j
    exact Complex.sub_im _ _
  have him : (z • (1 : Mat 4 ℂ) - Z.map Complex.ofReal).map Complex.im =
      η • (1 : Mat 4 ℝ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [z, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hij]
  change (((z • (1 : Mat 4 ℂ) - Z.map Complex.ofReal -
      phi (fun i => (y i : ℂ)) R).map Complex.im) - η • 1).PosSemidef
  rw [hsub, him, phi_imaginary]
  have hphi : phi y (-R.map Complex.im) = -phi y (R.map Complex.im) := by
    exact (phiLinear y).map_neg _
  have heq : η • (1 : Mat 4 ℝ) - phi y (R.map Complex.im) - η • 1 =
      phi y (-R.map Complex.im) := by
    rw [hphi]
    abel
  rw [heq]
  exact phi_posSemidef y _ hneg

theorem resolvent_schur_imaginary_posDef (X Z : Mat 4 ℝ) (hX : X.IsHermitian)
    (y : Fin 3 → ℝ) (a η : ℝ) (hη : 0 < η) :
    ((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat 4 ℂ) - Z.map Complex.ofReal -
      phi (fun i => (y i : ℂ))
        ((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat 4 ℂ) -
          X.map Complex.ofReal)⁻¹)).map Complex.im).PosDef := by
  have h := (Matrix.PosDef.one.smul hη).add_posSemidef
    (resolvent_schur_imaginary_lower_bound X Z hX y a η hη)
  simpa only [add_sub_cancel] using h

end Paper256

end

end OAI
