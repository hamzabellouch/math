import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SmallCoefficientRing
import OAI.GroupTheory.Thompson.InvariantMean

namespace OAI

/-! # An invariant mean on the actual bounded coefficient ring

Every ring element has finite range. Evaluation as a real bounded function is
therefore defined without any extra boundedness premise.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability
open scoped ENNReal
variable {G : Type} [Group G]

def smallCoefficientBoundedReal (f : SmallCoefficientRing G) : BoundedReal G := by
  refine ⟨fun x => (f.val x : ℝ), memℓp_infty ?_⟩
  apply ((booleanStepRing_finite_range (smallCoefficientFeature G) f).image
    (fun z : ℤ => ‖(z : ℝ)‖)).bddAbove.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨f.val x, ⟨x, rfl⟩, rfl⟩

@[simp]
theorem smallCoefficientBoundedReal_apply (f : SmallCoefficientRing G) (x : G) :
    smallCoefficientBoundedReal f x = (f.val x : ℝ) := rfl

def smallCoefficientBoundedRealLinear : SmallCoefficientRing G →ₗ[ℤ] BoundedReal G where
  toFun := smallCoefficientBoundedReal
  map_add' f h := by
    apply lp.ext
    funext x
    change ((f.val x + h.val x : ℤ) : ℝ) = (f.val x : ℝ) + (h.val x : ℝ)
    exact Int.cast_add _ _
  map_smul' n f := by
    apply lp.ext
    funext x
    change ((n • f.val x : ℤ) : ℝ) = n • (f.val x : ℝ)
    simp [zsmul_eq_mul]

@[simp]
theorem smallCoefficientBoundedReal_one :
    smallCoefficientBoundedReal (1 : SmallCoefficientRing G) = 1 := by
  apply lp.ext
  funext x
  exact Int.cast_one

theorem smallCoefficientBoundedReal_translate (g : G) (f : SmallCoefficientRing G) :
    smallCoefficientBoundedReal (g • f) = leftPull g⁻¹ (smallCoefficientBoundedReal f) := by
  apply lp.ext
  funext x
  rfl

def smallCoefficientRealMean (M : InvariantMean G) : SmallCoefficientRing G →ₗ[ℤ] ℝ :=
  (M.toLinearMap.restrictScalars ℤ).comp smallCoefficientBoundedRealLinear

@[simp]
theorem smallCoefficientRealMean_one (M : InvariantMean G) :
    smallCoefficientRealMean M 1 = 1 := by
  change M.toLinearMap (smallCoefficientBoundedReal 1) = 1
  rw [smallCoefficientBoundedReal_one, M.normalized]

theorem smallCoefficientRealMean_invariant (M : InvariantMean G)
    (g : G) (f : SmallCoefficientRing G) :
    smallCoefficientRealMean M (g • f) = smallCoefficientRealMean M f := by
  change M.toLinearMap (smallCoefficientBoundedReal (g • f)) = _
  rw [smallCoefficientBoundedReal_translate, M.left_invariant]
  rfl

end PolycyclicRecognition

end

end OAI
