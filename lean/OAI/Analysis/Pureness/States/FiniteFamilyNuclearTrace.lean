import OAI.Analysis.Pureness.States.FiniteFamilySpatialExtension
import OAI.Analysis.Pureness.States.FiniteFamilyTraceReduction
import OAI.Analysis.Pureness.States.FiniteFamilyRegularized
import OAI.Analysis.Pureness.States.RegularizedStateQuotientTrace
import OAI.Analysis.Pureness.States.RegularizedStateTraceIdentification

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
namespace CompatibleFiniteQuasitrace
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)

include hF in
lemma cauchyLevel_zero_nontrivial : Nontrivial (F.CauchyLevel hmono 0) := by
  apply nontrivial_of_ne (1 : F.CauchyLevel hmono 0) 0
  intro h
  let Q := (F.completedFamily hmono).toTwoQuasitrace.base
  have hu : Q 1=1 := (F.completedFamily hmono).toTwoQuasitrace_unit (F.completedFamily_unit hmono hF)
  have he := congrArg Q.toFun h
  rw [hu,Q.map_zero] at he
  exact one_ne_zero he

include hF in

theorem cauchyLevel_has_tracialState (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A) :
    Nonempty (TracialState (F.CauchyLevel hmono 0)) := by
  let T := F.positiveLevel hmono 1
  let ht := F.positiveLevel_metricSize_add hmono 1
  let : Nontrivial (T.CauchyQuotient ht) := F.cauchyLevel_zero_nontrivial hmono hF
  let : Nontrivial (FaithfulHilbertSpace (T.CauchyQuotient ht)) :=
    faithfulHilbertSpace_nontrivial (T.CauchyQuotient ht)
  exact tracialState_of_finite_freeGroup_tensor (T.cauchyTargetGNS ht)
    (F.spatialTensor_finite hmono hF hsimple hA)

end CompatibleFiniteQuasitrace

theorem nuclear_finiteBase_extreme_additive (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A) :
    (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceFunctions :=
  finiteBase_extreme_additive_of_cauchy_traces
    (fun F hmono hF _ => F.cauchyLevel_has_tracialState hmono hF hsimple hA)

theorem nuclear_finiteFamily_original_additive (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
    (F : CompatibleFiniteQuasitrace A)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
    (hF : F.level 1 1=1) :
    ∀ a b, F.toTwoQuasitrace.base (a+b)=F.toTwoQuasitrace.base a+F.toTwoQuasitrace.base b :=
  finiteQuasitrace_additive_of_base_extremePoints (nuclear_finiteBase_extreme_additive hsimple hA) F hmono hF

theorem nuclear_normalizedRegularizedState_additive (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    ∀ a b, (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base (a+b)=
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a+
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base b :=
  normalizedRegularizedState_additive_of_finiteBase_extremePoints hsimple y hy f
    (nuclear_finiteBase_extreme_additive hsimple hA)

theorem nuclear_regularizedState_agreeing_trace (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    ∃ τ : TracialState (RegularizedStateCauchyQuotient hsimple y hy f 0),
      ∀ x, τ.functional x=normalizedStateCauchyValue hsimple y hy f x :=
  (regularizedState_agreeing_trace_iff_original_additive hsimple y hy f).mpr
    (nuclear_normalizedRegularizedState_additive hsimple hA y hy f)
end CuntzPureness

end

end OAI
