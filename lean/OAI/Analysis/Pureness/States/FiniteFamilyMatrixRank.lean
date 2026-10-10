import OAI.Analysis.Pureness.States.FiniteFamilyMatrixTrace
import OAI.Analysis.Pureness.States.FiniteFamilyScalarRank

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

theorem nuclearRegularizedStateTrace_matrix_value_of_additive (n : ℕ)
    (hadd : ∀ M N, (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n (M+N)=
      (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n M+
      (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n N)
    (M : Positive (FinMatrix A n)) :
    sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)
      (Positive.map (matrixLimitStage n) M)=
      ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level n M.1).re) := by
  rw [sharedExtendedTrace_stage]
  congr 2
  exact ((normalizedRegularizedStateFiniteFamily hsimple y hy f).level_eq_matrixTrace_of_additive
    (nuclearRegularizedStateTrace hsimple hA y hy f)
    (fun a => (nuclearRegularizedStateTrace_apply hsimple hA y hy f a).trans
      (normalizedRegularizedStateFiniteFamily_base hsimple y hy f a).symm) n hadd M.1).symm

theorem nuclearRegularizedStateTrace_matrix_rank_of_additive (n : ℕ)
    (hadd : ∀ M N, (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n (M+N)=
      (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n M+
      (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n N)
    (M : Positive (FinMatrix A n)) :
    (sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)).rank
      (Positive.map (matrixLimitStage n) M)=
      (ENNReal.ofReal (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹)*
        regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n M) := by
  let τ := sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)
  rw [← ExtendedTrace.rank_pullback]
  have ht := (τ.pullback (matrixLimitStage n)).tendsto_roots_rank_all M
  let c : ℝ≥0 := ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
    inv_nonneg.mpr ENNReal.toReal_nonneg⟩
  have hr := finiteSpectralQuasitraceFamily_scaled_root_rank
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) c n M
  have he (k : ℕ) : τ.pullback (matrixLimitStage n) (Positive.power (Positive.rootExponent k) M)=
      ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level n
        (Positive.power (Positive.rootExponent k) M).1).re) :=
    nuclearRegularizedStateTrace_matrix_value_of_additive hsimple hA y hy f n hadd _
  simp only [he] at ht
  have hc : (c : ℝ≥0∞)=
      ENNReal.ofReal (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ :=
    (ENNReal.ofReal_coe_nnreal).symm
  rw [hc] at hr
  exact tendsto_nhds_unique ht hr
end CuntzPureness

end

end OAI
