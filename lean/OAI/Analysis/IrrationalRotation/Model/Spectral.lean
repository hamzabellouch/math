import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Invariant233

structure TracialState (A : Type*) [CStarAlgebra A] where
  toContinuousLinearMap : A →L[ℂ] ℂ
  map_one : toContinuousLinearMap 1 = 1
  map_star : ∀ a, toContinuousLinearMap (star a) = star (toContinuousLinearMap a)
  positive : ∀ a, 0 ≤ (toContinuousLinearMap (star a * a)).re
  tracial : ∀ a b, toContinuousLinearMap (a * b) = toContinuousLinearMap (b * a)

namespace TracialState

variable {A : Type*} [CStarAlgebra A]

instance : CoeFun (TracialState A) (fun _ => A → ℂ) :=
  ⟨fun τ => τ.toContinuousLinearMap⟩

end TracialState

def fugledeKadisonDeterminant {A : Type*} [CStarAlgebra A]
    (τ : TracialState A) (a : A) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r},
    ENNReal.ofReal (Real.exp ((τ (CFC.log (star a * a + (ε.val : ℝ) • (1 : A)))).re / 2))

def logarithmicPotentialDeterminant (μ : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r},
    ENNReal.ofReal (Real.exp ((∫ w, Real.log (‖w - z‖ ^ 2 + ε.val) ∂μ) / 2))

def IsBrownMeasure {A : Type*} [CStarAlgebra A]
    (τ : TracialState A) (a : A) (μ : Measure ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
    ∀ z : ℂ, fugledeKadisonDeterminant τ (a - algebraMap ℂ A z) =
      logarithmicPotentialDeterminant μ z

end Invariant233

end

end OAI
