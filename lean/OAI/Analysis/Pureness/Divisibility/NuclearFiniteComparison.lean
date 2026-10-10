import OAI.Analysis.Pureness.Divisibility.NuclearFiniteFamilyAdditivity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped ENNReal NNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem nuclear_finiteComparison_of_tracialRanks (hsimple : TopologicallySimple A)
    (hA : IsNuclear.{u,0} A)
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (L : ℕ) (M N : Positive (FinMatrix A L)) (hN : N.1 ≠ 0)
    (hgap : ∀ τ : TracialState A,
      (sharedExtendedTrace τ).rank (Positive.map (matrixLimitStage L) M) <
      (sharedExtendedTrace τ).rank (Positive.map (matrixLimitStage L) N)) :
    CuntzSubequiv M.1 N.1 := by
  have hy : finitePositiveClass L N ≠ 0 := fun h => hN ((finitePositiveClass_eq_zero_iff L N).mp h)
  have hcut : ∀ ε : ℝ≥0, 0 < ε → CuntzSubequiv (Positive.cut ε M).1 N.1 := by
    intro ε hε
    apply finiteComparison_of_states hsimple hAU L (Positive.cut ε M) N hN
    intro f
    let d := regularizedFiniteDimension f.toAddHom f.monotone
    have hg := hgap (nuclearRegularizedStateTrace hsimple hA _ hy f)
    rw [nuclearRegularizedStateTrace_matrix_rank,nuclearRegularizedStateTrace_matrix_rank] at hg
    have hu := finiteState_regularized_unit hsimple _ hy f
    have hc : ENNReal.ofReal (d finiteUnitClass).toReal⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (ENNReal.toReal_pos hu.1.ne' hu.2))).ne'
    have hd : d (finitePositiveClass L M) < d (finitePositiveClass L N) :=
      (ENNReal.mul_lt_mul_iff_right hc ENNReal.ofReal_ne_top).mp hg
    have hleft : f.1 (finitePositiveClass L (Positive.cut ε M)) ≤ d (finitePositiveClass L M) := by
      rw [show d (finitePositiveClass L M) = finiteRegularizedValue f.toAddHom L M from
        regularizedFiniteDimension_eval f.toAddHom f.monotone L M]
      exact cut_class_value_le_regularized f.toAddHom L M ε hε
    have hright : d (finitePositiveClass L N) ≤ 1 :=
      (regularizedFiniteDimension_le f.toAddHom f.monotone _).trans f.at_unit.le
    exact (hleft.trans_lt hd).trans_le hright
  let ε : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0)+1)
  have hε : Filter.Tendsto (fun j => (ε j : ℝ)) Filter.atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ)+1)) Filter.atTop (nhds 0))
  exact cuntzSubequiv_of_tendsto (fun j => hcut (ε j) (by dsimp [ε]; positivity))
    ((continuous_subtype_val.tendsto M).comp (Positive.tendsto_cut ε hε M))
end CuntzPureness

end

end OAI
