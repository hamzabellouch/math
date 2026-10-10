import OAI.Analysis.Pureness.States.CauchyQuotientAdditivity
import OAI.Analysis.Pureness.Quasitrace.AdditiveQuasitraceTrace
import OAI.Analysis.Pureness.Quasitrace.QuasitraceExtremalReduction
import OAI.Analysis.Pureness.States.NormalizedStateQuotientTwoQuasitrace
import OAI.Analysis.Pureness.Cuntz.FinOneMatrixTransport

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

theorem normalizedStateCauchyValue_add_iff_original :
    (∀ x z : RegularizedStateCauchyQuotient hsimple y hy f 0,
      normalizedStateCauchyValue hsimple y hy f (x+z) =
        normalizedStateCauchyValue hsimple y hy f x + normalizedStateCauchyValue hsimple y hy f z) ↔
    (∀ a b : A, (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base (a+b) =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a +
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base b) := by
  constructor
  · intro h a b
    let e := (regularizedStateCauchyEmbedding hsimple y hy f 0).comp
      (scalarMatrixHom (ι := Fin 1) (A := A))
    calc
      _ = normalizedStateCauchyValue hsimple y hy f (e (a+b)) :=
        (normalizedStateCauchyValue_original hsimple y hy f (a+b)).symm
      _ = normalizedStateCauchyValue hsimple y hy f (e a+e b) :=
        congrArg (normalizedStateCauchyValue hsimple y hy f) (map_add e a b)
      _ = normalizedStateCauchyValue hsimple y hy f (e a)+
          normalizedStateCauchyValue hsimple y hy f (e b) := h (e a) (e b)
      _ = _ := congrArg₂ (·+·)
        (normalizedStateCauchyValue_original hsimple y hy f a)
        (normalizedStateCauchyValue_original hsimple y hy f b)
  · intro h x z
    let d := regularizedFiniteDimension f.toAddHom f.monotone
    let hd := regularizedFiniteDimension_monotone f.toAddHom f.monotone
    let hl := regularizedState_dimension_lsc y f
    let hf := regularizedState_dimension_finite hsimple y hy f
    let T := finiteSpectralPositiveQuasitrace d hd hl hf 1
    let hm := finiteSpectralPositiveQuasitrace_metricSize_add d hd hl hf 1
    let hs := finiteSpectralPositiveQuasitrace_sqrt_add d hd hl hf 1
    let c : ℂ := ((d finiteUnitClass).toReal⁻¹ : ℂ)
    have horig (a : A) : c*T.complexValue (scalarMatrixHom (ι := Fin 1) a) =
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a := by
      have he := normalizedStateCauchyValue_original hsimple y hy f a
      unfold normalizedStateCauchyValue regularizedStateCauchyEmbedding at he
      rw [finiteQuasitraceCauchyValue_embedding] at he
      exact he
    have hlin (M N : FinMatrix A 1) :
        c*T.complexValue (M+N) = c*T.complexValue M+c*T.complexValue N := by
      obtain ⟨a, rfl⟩ := scalarMatrixHom_finOne_bijective.2 M
      obtain ⟨b, rfl⟩ := scalarMatrixHom_finOne_bijective.2 N
      exact (congrArg (fun M => c*T.complexValue M)
        (map_add (scalarMatrixHom (ι := Fin 1) (A := A)) a b).symm).trans
        ((horig (a+b)).trans ((h a b).trans
          (congrArg₂ (·+·) (horig a).symm (horig b).symm)))
    exact T.scaled_quotientValue_add hm hs c hlin x z

theorem regularizedState_agreeing_trace_iff_original_additive :
    (∃ τ : TracialState (RegularizedStateCauchyQuotient hsimple y hy f 0),
      ∀ x, τ.functional x = normalizedStateCauchyValue hsimple y hy f x) ↔
    (∀ a b : A, (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base (a+b) =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a +
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base b) := by
  have ht := (normalizedStateQuotientQuasitrace hsimple y hy f).exists_tracialState_agreeing_iff
    (normalizedStateQuotientQuasitrace_unit hsimple y hy f)
  simp only [normalizedStateQuotientQuasitrace_eq] at ht
  exact ht.trans (normalizedStateCauchyValue_add_iff_original hsimple y hy f)

theorem regularizedState_agreeing_trace_of_extreme_additivity
    (hext : (normalizedQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceCoordinates) :
    ∃ τ : TracialState (RegularizedStateCauchyQuotient hsimple y hy f 0),
      ∀ x, τ.functional x = normalizedStateCauchyValue hsimple y hy f x := by
  apply (regularizedState_agreeing_trace_iff_original_additive hsimple y hy f).mpr
  exact normalizedQuasitrace_additive_of_extremePoints hext
    (normalizedRegularizedStateTwoQuasitrace hsimple y hy f)
    (normalizedRegularizedStateTwoQuasitrace_unit hsimple y hy f)
end CuntzPureness

end

end OAI
