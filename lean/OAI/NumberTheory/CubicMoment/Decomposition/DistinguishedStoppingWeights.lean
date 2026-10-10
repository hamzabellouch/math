import OAI.NumberTheory.CubicMoment.Estimates.NormPartitionVariation
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedScalePartition

namespace OAI

/-! The distinguished scale coefficients use a single bounded-variation
family at every partition scale, exactly as the stopped estimate requires. -/
noncomputable section
open Filter
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedStoppingWeights {i N : ℕ} (k : Fin i → Fin N)
    (j : Fin i) (x : ℝ) : ℂ := scaledNormPartitionWeight (2/(4/3:ℝ)^(k j).val) x

lemma distinguishedStoppingWeights_at {i N : ℕ} (k : Fin i → Fin N)
    (j : Fin i) (p : Eisenstein) :
    distinguishedStoppingWeights k j (norm p) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k j).val) := by
  unfold distinguishedStoppingWeights scaledNormPartitionWeight
  congr 1
  ring

theorem distinguishedStoppingWeights_uniform :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (i N : ℕ) (k : Fin i → Fin N),
      (∀ j x, ‖distinguishedStoppingWeights k j x‖ ≤ 1) ∧
      (∀ j, ContDiff ℝ ∞ (distinguishedStoppingWeights k j)) ∧
      (∀ j x, 0 < x → ‖deriv (distinguishedStoppingWeights k j) x‖*x ≤ V) := by
  obtain ⟨V,hV,hbound⟩ := scaledNormPartitionWeight_deriv_bound
  refine ⟨V,hV,?_⟩
  intro i N k
  exact ⟨fun _ _ => scaledNormPartitionWeight_norm _ _,
    fun _ => scaledNormPartitionWeight_smooth _,
    fun j x hx => hbound _ (by positivity) x hx⟩

end CubicFirstMoment

end

end OAI
