import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileStateInterpretation

namespace OAI

/-! The computed K=34 majorant bounds the actual parameter-dependent product. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

private theorem prefix_remainder (ns : List ℕ) (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    let s := ns.foldr step initial
    Dominates ((radius : ℝ)^2 • rationalMatrix s.error)
      ((ns.map (profileFactor ((centerB : ℝ)+b) ((centerZ : ℝ)+z))).prod-
        linearModel (complexMatrix s.value) (complexMatrix s.derivB) (complexMatrix s.derivZ) b z) := by
  induction ns with
  | nil =>
      dsimp only [List.foldr_nil]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [initial, linearModel, complexMatrix, rationalMatrix, Matrix2.zero,
          Matrix2.one, Matrix2.toMatrix]
  | cons n ns ih =>
      dsimp only at ih ⊢
      rw [List.foldr_cons, List.map_cons, List.prod_cons, profileFactor_affine,
        state_value_step, state_derivB_step, state_derivZ_step, state_error_step,
        Matrix.smul_mul]
      exact taylor_step_dominates _ _ _ _ _ _ _ _ _ _ _ _ _ b z (radius : ℝ)
        (((n : ℝ)+1)⁻¹) (by positivity) hb hz
        (absoluteMatrix_dominates (factor n)) (absoluteMatrix_dominates parameterB)
        (absoluteMatrix_dominates parameterZ) (absoluteMatrix_dominates _)
        (absoluteMatrix_dominates _) ih

/-- Parameter-uniform Taylor remainder with the precise certificate matrix E. -/
theorem profileProduct_remainder (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    Dominates ((radius : ℝ)^2 • rationalMatrix result.error)
      (profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34-
        linearModel (complexMatrix result.value) (complexMatrix result.derivB)
          (complexMatrix result.derivZ) b z) := by
  simpa only [profileFactor_product, result] using prefix_remainder (List.range 34) b z hb hz

end DefocusingNLS.ProfileCertificate

end OAI
