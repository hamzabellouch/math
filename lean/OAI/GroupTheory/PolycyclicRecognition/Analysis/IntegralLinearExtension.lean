import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBilinearExtension

namespace OAI

/-! # Extending finite integral linear automorphisms to real coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {d e : ℕ}

def realLinearExtension (f : (Fin d → ℤ) →ₗ[ℤ] (Fin e → ℤ)) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ) :=
  (Pi.basisFun ℝ (Fin d)).constr ℝ
    (fun i => integerVectorMap e (f ((Pi.basisFun ℤ (Fin d)) i)))

theorem integerVectorMap_basis (i : Fin d) :
    integerVectorMap d ((Pi.basisFun ℤ (Fin d)) i) = (Pi.basisFun ℝ (Fin d)) i := by
  ext j
  by_cases h : i = j
  · subst j
    simp [integerVectorMap, Pi.basisFun_apply]
  · simp [integerVectorMap, Pi.basisFun_apply, Ne.symm h]

theorem realLinearExtension_basis (f : (Fin d → ℤ) →ₗ[ℤ] (Fin e → ℤ)) (i : Fin d) :
    realLinearExtension f ((Pi.basisFun ℝ (Fin d)) i) =
      integerVectorMap e (f ((Pi.basisFun ℤ (Fin d)) i)) := by
  exact (Pi.basisFun ℝ (Fin d)).constr_basis ℝ _ i

theorem realLinearExtension_cast (f : (Fin d → ℤ) →ₗ[ℤ] (Fin e → ℤ)) (x : Fin d → ℤ) :
    realLinearExtension f (integerVectorMap d x) = integerVectorMap e (f x) := by
  have hx : ∑ i, x i • (Pi.basisFun ℤ (Fin d)) i = x := by
    simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
      (Pi.basisFun ℤ (Fin d)).sum_equivFun x
  calc
    realLinearExtension f (integerVectorMap d x) =
        ∑ i, (x i : ℝ) • integerVectorMap e (f ((Pi.basisFun ℤ (Fin d)) i)) := by
      simp only [realLinearExtension, Basis.constr_apply_fintype,
        Pi.basisFun_equivFun, LinearEquiv.refl_apply]
      rfl
    _ = integerVectorMap e (f (∑ i, x i • (Pi.basisFun ℤ (Fin d)) i)) := by
      simp only [map_sum, map_smul, Int.cast_smul_eq_zsmul, map_zsmul]
    _ = integerVectorMap e (f x) := by rw [hx]

def realIntegralLinearEquiv (A : (Fin d → ℤ) ≃ₗ[ℤ] (Fin e → ℤ)) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin e → ℝ) where
  toLinearMap := realLinearExtension A.toLinearMap
  invFun := realLinearExtension A.symm.toLinearMap
  left_inv := by
    have h : (realLinearExtension A.symm.toLinearMap).comp
        (realLinearExtension A.toLinearMap) = LinearMap.id := by
      apply (Pi.basisFun ℝ (Fin d)).ext
      intro i
      simp only [LinearMap.comp_apply, realLinearExtension_basis, realLinearExtension_cast,
        LinearMap.id_apply]
      change integerVectorMap d (A.symm (A _)) = _
      rw [LinearEquiv.symm_apply_apply, integerVectorMap_basis]
    exact congrFun (congrArg DFunLike.coe h)
  right_inv := by
    have h : (realLinearExtension A.toLinearMap).comp
        (realLinearExtension A.symm.toLinearMap) = LinearMap.id := by
      apply (Pi.basisFun ℝ (Fin e)).ext
      intro i
      simp only [LinearMap.comp_apply, realLinearExtension_basis, realLinearExtension_cast,
        LinearMap.id_apply]
      change integerVectorMap e (A (A.symm _)) = _
      rw [LinearEquiv.apply_symm_apply, integerVectorMap_basis]
    exact congrFun (congrArg DFunLike.coe h)

theorem realIntegralLinearEquiv_cast (A : (Fin d → ℤ) ≃ₗ[ℤ] (Fin e → ℤ)) (x : Fin d → ℤ) :
    realIntegralLinearEquiv A (integerVectorMap d x) = integerVectorMap e (A x) :=
  realLinearExtension_cast A.toLinearMap x

end PolycyclicRecognition

end

end OAI
