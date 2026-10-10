import OAI.Analysis.Pureness.States.RegularizedStateQuasitrace
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNormBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def ComplexQuasitrace.scale (T : ComplexQuasitrace A) (c : ℝ≥0) : ComplexQuasitrace A where
  toFun x := (c : ℂ)*T x
  polar x := congrArg ((c : ℂ)*·) (T.polar x)
  square_nonneg x := mul_nonneg (by exact_mod_cast c.2) (T.square_nonneg x)
  real_add_I a b := by rw [T.real_add_I]; ring
  abelian_linear S _ := by
    obtain ⟨f,hf⟩ := T.abelian_linear S
    refine ⟨(c : ℂ) • f,?_⟩
    intro x
    change (c : ℂ)*f x = _
    rw [hf]

def TwoQuasitrace.scale (T : TwoQuasitrace A) (c : ℝ≥0) : TwoQuasitrace A where
  base := T.base.scale c
  matrix := T.matrix.scale c
  extension x := congrArg ((c : ℂ)*·) (T.extension x)

lemma TwoQuasitrace.scale_unit (T : TwoQuasitrace A) (u : ℝ) (hu : 0 < u)
    (hunit : T.base 1 = (u : ℂ)) :
    (T.scale ⟨u⁻¹,inv_nonneg.mpr hu.le⟩).base 1 = 1 := by
  change (u⁻¹ : ℝ)*(T.base 1) = (1 : ℂ)
  rw [hunit,← Complex.ofReal_mul,inv_mul_cancel₀ hu.ne',Complex.ofReal_one]

variable [Nontrivial A]

def normalizedRegularizedStateTwoQuasitrace (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) : TwoQuasitrace A :=
  (regularizedStateTwoQuasitrace hsimple y hy f).scale
    ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
      inv_nonneg.mpr ENNReal.toReal_nonneg⟩

theorem normalizedRegularizedStateTwoQuasitrace_unit (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base 1 = 1 := by
  apply TwoQuasitrace.scale_unit
  · exact ENNReal.toReal_pos (finiteState_regularized_unit hsimple y hy f).1.ne'
      (finiteState_regularized_unit hsimple y hy f).2
  · exact finiteSpectralTwoQuasitrace_unit _ _ _ _

theorem regularizedState_positiveQuasitrace_faithful (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : M.1 ≠ 0) :
    0 < finiteSpectralPositiveQuasitrace
      (regularizedFiniteDimension f.toAddHom f.monotone)
      (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
      (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) n M :=
  ENNReal.toReal_pos (regularizedState_integral_positive hsimple y hy f n M hM).ne'
    (regularizedState_integral_finite hsimple y hy f n M)
end CuntzPureness

end

end OAI
