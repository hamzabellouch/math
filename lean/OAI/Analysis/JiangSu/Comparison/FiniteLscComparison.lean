import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FiniteStateComparison
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteStateRegularization

namespace OAI


noncomputable section
namespace Pureness
open TraceCone OrderedSemigroup
open scoped ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem finiteState_regularized_unit (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    0 < regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass ∧
      regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass ≠ ⊤ := by
  have heq : regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass = f.1 finiteUnitClass :=
    regularizedFiniteDimension_projection f.toAddHom f.monotone 1 ⟨1,zero_le_one⟩
      IsIdempotentElem.one
  rw [heq]
  exact finiteState_unit_pos hsimple y hy f

theorem finiteComparison_of_lscDimensions (hsimple : TopologicallySimple A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (L : ℕ) (M N : Positive (FinMatrix A L)) (hN : N.1 ≠ 0)
    (hgap : ∀ (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞), Monotone d →
      (∀ n, LowerSemicontinuous (fun Q : Positive (FinMatrix A n) => d (finitePositiveClass n Q))) →
      0 < d finiteUnitClass → d finiteUnitClass ≠ ⊤ →
      d (finitePositiveClass L M) < d (finitePositiveClass L N)) :
    CuntzSubequiv M.1 N.1 := by
  have hcut : ∀ ε : ℝ≥0, 0 < ε → CuntzSubequiv (Positive.cut ε M).1 N.1 := by
    intro ε hε
    apply finiteComparison_of_states hsimple hAU L (Positive.cut ε M) N hN
    intro f
    let d := regularizedFiniteDimension f.toAddHom f.monotone
    have hd : Monotone d := regularizedFiniteDimension_monotone f.toAddHom f.monotone
    have hlsc : ∀ n, LowerSemicontinuous (fun Q : Positive (FinMatrix A n) => d (finitePositiveClass n Q)) := by
      intro n
      have heq : (fun Q : Positive (FinMatrix A n) => d (finitePositiveClass n Q)) =
          finiteRegularizedValue f.toAddHom n :=
        funext (fun Q => regularizedFiniteDimension_eval f.toAddHom f.monotone n Q)
      rw [heq]
      exact finiteRegularizedValue_lowerSemicontinuous f.toAddHom f.monotone n
    have hy : finitePositiveClass L N ≠ 0 := fun h => hN ((finitePositiveClass_eq_zero_iff L N).mp h)
    have hdu := finiteState_regularized_unit hsimple _ hy f
    have hg := hgap d hd hlsc hdu.1 hdu.2
    have hleft : f.1 (finitePositiveClass L (Positive.cut ε M)) ≤ d (finitePositiveClass L M) := by
      rw [show d (finitePositiveClass L M) = finiteRegularizedValue f.toAddHom L M from
        regularizedFiniteDimension_eval f.toAddHom f.monotone L M]
      exact cut_class_value_le_regularized f.toAddHom L M ε hε
    have hright : d (finitePositiveClass L N) ≤ 1 :=
      (regularizedFiniteDimension_le f.toAddHom f.monotone _).trans f.at_unit.le
    exact (hleft.trans_lt hg).trans_le hright
  let ε : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0)+1)
  have hε : Filter.Tendsto (fun j => (ε j : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [ε, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ)+1)) Filter.atTop (nhds 0))
  exact cuntzSubequiv_of_tendsto (fun j => hcut (ε j) (by dsimp [ε]; positivity))
    ((continuous_subtype_val.tendsto M).comp (Positive.tendsto_cut ε hε M))

end Pureness
end

end OAI
