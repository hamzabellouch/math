import OAI.Analysis.HyperbolicCones.TangentBasic
import OAI.Analysis.HyperbolicCones.OperatorEntries
import OAI.Analysis.HyperbolicCones.FormRigidity

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace Paper256

theorem impossible_of_tangent_formula (P : NormalizedPencil)
    (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ)
    (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0)
    (hformula : ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
      choiLam (wedgeCoordinates v h) y =
        operatorNorm (P.leftProjection v * P.B y * T h) ^ 2) : False := by
  obtain ⟨J, hJ⟩ := tangent_coordinates_isomorphism v hv hv0
  let D : (Fin 3 → ℝ) →ₗ[ℝ] Mat P.c ℝ :=
    T.comp ((tangentSpace v).subtype.comp J.symm.toLinearMap)
  let C : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin P.a) (Fin P.c) ℝ :=
    (mulLeftLinearMap (Fin P.c) ℝ (P.leftProjection v)).comp P.B
  let b : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin P.a) (Fin P.c) ℝ :=
    (mulLinearMap ℝ).flip.compl₁₂ D C
  have hb (z y : Fin 3 → ℝ) : choiLam z y = operatorNorm (b z y) ^ 2 := by
    have ht : inner ℝ v (J.symm z).val = 0 := (J.symm z).property
    have hj : wedgeCoordinates v (J.symm z).val = z := by
      rw [← hJ, J.apply_symm_apply]
    change choiLam z y = operatorNorm (P.leftProjection v * P.B y * T (J.symm z).val) ^ 2
    simpa only [hj] using hformula (J.symm z).val ht y
  have hz (z y : Fin 3 → ℝ) : b z y = 0 := by
    ext i j
    let l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
      b.compr₂ (Matrix.entryLinearMap ℝ ℝ i j)
    have hl : l = 0 := choiLam_no_dominated_square l (fun z y => by
      change (b z y i j) ^ 2 ≤ choiLam z y
      rw [hb]
      exact entry_sq_le_operatorNorm_sq (b z y) i j)
    have he := LinearMap.congr_fun (LinearMap.congr_fun hl z) y
    exact he
  have hc := hb ![1, 0, 0] ![1, 0, 0]
  rw [choiLam_nonzero, hz, operatorNorm_eq_norm, norm_zero, zero_pow (by decide)] at hc
  exact one_ne_zero hc

end Paper256

end

end OAI
