import OAI.Analysis.Pureness.Projections.FiniteSpectralTwoQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

omit [Nontrivial A] in
lemma regularizedState_dimension_finite (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (x : finiteCuntzSubmonoid (A := A)) :
    regularizedFiniteDimension f.toAddHom f.monotone x ≠ ⊤ :=
  ne_top_of_le_ne_top (finiteCuntz_state_finite hsimple y hy f x)
    (regularizedFiniteDimension_le f.toAddHom f.monotone x)

omit [Nontrivial A] in
lemma regularizedState_dimension_lsc (y : finiteCuntzSubmonoid (A := A)) (f : StateSpace y) (n : ℕ) :
    LowerSemicontinuous (fun M : Positive (FinMatrix A n) =>
      regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n M)) := by
  have he : (fun M : Positive (FinMatrix A n) =>
      regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n M)) =
      finiteRegularizedValue f.toAddHom n :=
    funext (regularizedFiniteDimension_eval f.toAddHom f.monotone n)
  rw [he]
  exact finiteRegularizedValue_lowerSemicontinuous f.toAddHom f.monotone n

def regularizedStateTwoQuasitrace (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) : TwoQuasitrace A :=
  finiteSpectralTwoQuasitrace (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)

theorem regularizedStateTwoQuasitrace_unit_pos (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    0 < (regularizedStateTwoQuasitrace hsimple y hy f).base 1 := by
  rw [regularizedStateTwoQuasitrace,finiteSpectralTwoQuasitrace_unit]
  apply Complex.zero_lt_real.mpr
  exact ENNReal.toReal_pos (finiteState_regularized_unit hsimple y hy f).1.ne'
    (finiteState_regularized_unit hsimple y hy f).2

omit [Nontrivial A] in
theorem regularizedStateQuasitrace_root_rank (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Filter.Tendsto (fun k => ENNReal.ofReal (((finiteSpectralQuasitraceFamily
      (regularizedFiniteDimension f.toAddHom f.monotone)
      (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
      (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)).level n
      (Positive.power (Positive.rootExponent k) M).1).re)) Filter.atTop
      (nhds (regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n M))) :=
  finiteSpectralQuasitraceFamily_root_rank _ _ _ _ n M
end CuntzPureness

end

end OAI
