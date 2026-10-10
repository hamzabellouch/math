import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import OAI.Analysis.Pureness.Comparison.TraceAlgebra

namespace OAI
open scoped ComplexOrder

namespace CuntzComparison

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure TracialState extends A →ₚ[ℂ] ℂ where
  normalized : toPositiveLinearMap 1 = 1
  tracial : ∀ a b, toPositiveLinearMap (a * b) = toPositiveLinearMap (b * a)

variable {A}

namespace TracialState

noncomputable def algebraicTrace (τ : TracialState A) : AlgebraicTrace A ℂ where
  toAddMonoidHom := τ.toPositiveLinearMap.toLinearMap.toAddMonoidHom
  cyclic := τ.tracial

noncomputable def twoNorm (τ : TracialState A) (a : A) : ℝ :=
  ‖τ.toPositiveLinearMap.toPreGNS a‖

theorem twoNorm_eq (τ : TracialState A) (a : A) :
    τ.twoNorm a = Real.sqrt (τ.toPositiveLinearMap (star a * a)).re := by
  rfl

theorem twoNorm_nonneg (τ : TracialState A) (a : A) : 0 ≤ τ.twoNorm a := norm_nonneg _

@[simp] theorem twoNorm_zero (τ : TracialState A) : τ.twoNorm 0 = 0 := by
  simp [twoNorm]

@[simp] theorem twoNorm_one (τ : TracialState A) : τ.twoNorm 1 = 1 := by
  simp [twoNorm_eq, τ.normalized]

theorem twoNorm_add_le (τ : TracialState A) (a b : A) :
    τ.twoNorm (a + b) ≤ τ.twoNorm a + τ.twoNorm b := by
  simpa [twoNorm] using norm_add_le (τ.toPositiveLinearMap.toPreGNS a)
    (τ.toPositiveLinearMap.toPreGNS b)

theorem twoNorm_smul (τ : TracialState A) (z : ℂ) (a : A) :
    τ.twoNorm (z • a) = ‖z‖ * τ.twoNorm a := by
  simp [twoNorm, norm_smul]

@[simp] theorem twoNorm_star (τ : TracialState A) (a : A) :
    τ.twoNorm (star a) = τ.twoNorm a := by
  simp only [twoNorm_eq, star_star, τ.tracial a (star a)]

theorem twoNorm_mul_left (τ : TracialState A) (a b : A) :
    τ.twoNorm (a * b) ≤ ‖a‖ * τ.twoNorm b := by
  let f := τ.toPositiveLinearMap
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    τ.twoNorm (a * b) = ‖f.leftMulMapPreGNS a (f.toPreGNS b)‖ := rfl
    _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS b‖ :=
      (f.leftMulMapPreGNS a).le_opNorm _
    _ ≤ ‖a‖ * τ.twoNorm b := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

theorem twoNorm_mul_right (τ : TracialState A) (a b : A) :
    τ.twoNorm (b * a) ≤ ‖a‖ * τ.twoNorm b := by
  calc
    τ.twoNorm (b * a) = τ.twoNorm (star a * star b) := by
      rw [← star_mul, twoNorm_star]
    _ ≤ ‖star a‖ * τ.twoNorm (star b) := τ.twoNorm_mul_left _ _
    _ = ‖a‖ * τ.twoNorm b := by rw [norm_star, twoNorm_star]

theorem twoNorm_le_norm (τ : TracialState A) (a : A) : τ.twoNorm a ≤ ‖a‖ := by
  simpa using τ.twoNorm_mul_left a 1

noncomputable def toPreGNSContinuous (τ : TracialState A) :
    A →L[ℂ] τ.toPositiveLinearMap.PreGNS :=
  τ.toPositiveLinearMap.toPreGNS.toLinearMap.mkContinuous 1
    (fun a => by simpa [twoNorm] using τ.twoNorm_le_norm a)

theorem continuous_twoNorm (τ : TracialState A) : Continuous τ.twoNorm :=
  τ.toPreGNSContinuous.continuous.norm

end TracialState
end CuntzComparison

end OAI
