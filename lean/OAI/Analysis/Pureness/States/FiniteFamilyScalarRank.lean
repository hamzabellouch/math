import OAI.Analysis.Pureness.States.FiniteFamilyNuclearTrace
import OAI.Analysis.Pureness.Quasitrace.QuasitraceScaledRank
import OAI.Analysis.Pureness.Completion.CompletedSharedTrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def nuclearRegularizedStateTrace : TracialState A :=
  (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base.tracialStateOfAdditive
    (normalizedRegularizedStateTwoQuasitrace_unit hsimple y hy f)
    (nuclear_normalizedRegularizedState_additive hsimple hA y hy f)

lemma nuclearRegularizedStateTrace_apply (a : A) :
    (nuclearRegularizedStateTrace hsimple hA y hy f).functional a =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a :=
  ComplexQuasitrace.additiveLinear_apply _ _ a

lemma nuclearRegularizedStateTrace_finOne_value (M : Positive (FinMatrix A 1)) :
    sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)
      (Positive.map (matrixLimitStage 1) M) =
    ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level 1 M.1).re) := by
  rw [sharedExtendedTrace_stage]
  change ENNReal.ofReal ((∑ i : Fin 1,
    (nuclearRegularizedStateTrace hsimple hA y hy f).functional (M.1 i i)).re) = _
  rw [Fin.sum_univ_one, nuclearRegularizedStateTrace_apply,
    ← normalizedRegularizedStateFiniteFamily_base]
  change ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level 1
    (scalarMatrixHom (ι := Fin 1) (M.1 0 0))).re) = _
  have he : scalarMatrixHom (ι := Fin 1) (M.1 0 0) = M.1 := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he]

theorem nuclearRegularizedStateTrace_finOne_rank (M : Positive (FinMatrix A 1)) :
    (sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)).rank
      (Positive.map (matrixLimitStage 1) M) =
    (ENNReal.ofReal (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹)*
      regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass 1 M) := by
  let τ := sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)
  rw [← ExtendedTrace.rank_pullback]
  have ht := (τ.pullback (matrixLimitStage 1)).tendsto_roots_rank_all M
  let c : ℝ≥0 := ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
    inv_nonneg.mpr ENNReal.toReal_nonneg⟩
  have hr := finiteSpectralQuasitraceFamily_scaled_root_rank
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)
    c 1 M
  have he (k : ℕ) : τ.pullback (matrixLimitStage 1) (Positive.power (Positive.rootExponent k) M) =
      ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level 1
        (Positive.power (Positive.rootExponent k) M).1).re) :=
    nuclearRegularizedStateTrace_finOne_value hsimple hA y hy f _
  simp only [he] at ht
  have hc : (c : ℝ≥0∞) =
      ENNReal.ofReal (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ :=
    (ENNReal.ofReal_coe_nnreal).symm
  rw [hc] at hr
  exact tendsto_nhds_unique ht hr
end CuntzPureness

end

end OAI
