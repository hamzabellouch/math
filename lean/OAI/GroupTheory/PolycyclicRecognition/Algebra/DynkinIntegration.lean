import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSmoothHom
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords

namespace OAI

/-! # Integration from a common finite BCH formula

A common two-factor BCH formula for the source and target makes
exponential conjugation of a Lie algebra homomorphism multiplicative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]
  (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
  (cH : GroupLieAlgebra (𝓘(ℝ, F)) H ≃ₜ H)
  (hG : IsGroupExponential cG) (hH : IsGroupExponential cH)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hprodG : ∀ x y, cG x * cG y = cG (finiteDynkinPolynomial coeff ![x, y]))
  (hprodH : ∀ x y, cH x * cH y = cH (finiteDynkinPolynomial coeff ![x, y]))
  (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, F)) H)

def exponentialHomOfDynkin : G →* H where
  toFun g := cH (j (cG.symm g))
  map_one' := by
    erw [← hG.map_zero, Homeomorph.symm_apply_apply, map_zero]
    exact hH.map_zero
  map_mul' g k := by
    obtain ⟨x, rfl⟩ := cG.surjective g
    obtain ⟨y, rfl⟩ := cG.surjective k
    erw [hprodG, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
      Homeomorph.symm_apply_apply, hprodH, finiteDynkinPolynomial_map]
    congr 2
    funext i
    fin_cases i <;> rfl

@[simp] theorem exponentialHomOfDynkin_apply_exp
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j (cG x) = cH (j x) := by
  change cH (j (cG.symm (cG x))) = _
  rw [Homeomorph.symm_apply_apply]

theorem continuous_exponentialHomOfDynkin :
    Continuous (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) :=
  cH.continuous.comp (j.toLinearMap.continuous_of_finiteDimensional.comp cG.symm.continuous)

theorem contMDiff_exponentialHomOfDynkin :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞
      (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) :=
  contMDiff_of_exponential_compatibility hG hH _
    (continuous_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j)
    j.toLinearMap (exponentialHomOfDynkin_apply_exp cG cH hG hH coeff hprodG hprodH j)

theorem mfderiv_exponentialHomOfDynkin [T2Space H]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F))
      (exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j) 1 x = j x :=
  mfderiv_eq_of_exponential_compatibility hG hH _
    ((contMDiff_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j).mdifferentiable
      (by simp)) j.toLinearMap
    (exponentialHomOfDynkin_apply_exp cG cH hG hH coeff hprodG hprodH j) x

end PolycyclicRecognition

end

end OAI
