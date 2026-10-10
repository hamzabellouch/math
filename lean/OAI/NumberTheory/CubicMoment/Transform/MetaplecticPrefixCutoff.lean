import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCodePartition
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualFinite

namespace OAI

/-! The original retained-frequency cutoff also bounds the d and supported
cube-factor projections used in the arithmetic prefix sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_prefix_cube_dvd {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) :
    p.2.2.2.2.val ∣ (metaplecticPrefixArgument r p.2 w).val := by
  rw [metaplecticPrefixArgument,metaplecticFreeArgument_val _ _ _ _ hw]
  refine ⟨lambdaE^p.2.1*p.2.2.1.val*p.2.2.2.1.val*w*p.2.2.2.2.val^2,?_⟩
  dsimp only [metaplecticDivisorPrimary]
  ring

lemma metaplectic_prefix_cutoff {r : Eisenstein}
    (S : Finset (MetaplecticRetainedCode r)) {I : ℝ}
    (hS : ∀ z ∈ S, metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I) :
    ∀ p ∈ S.image metaplecticCodePrefix,
      norm p.1 ≤ 3*I ∧ norm p.2.2.2.2 ≤ 3*I := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  have hbound := metaplecticDualNorm_coordinate_bound _ (hS z hz)
  refine ⟨hbound.2,?_⟩
  have hdiv := metaplectic_prefix_cube_dvd (r := r) (metaplecticCodePrefix z)
    (primary_ne_zero z.2.2.property)
  have hn := norm_le_of_dvd (metaplecticRetainedDecode r z).1.property hdiv
  exact hn.trans hbound.1

lemma metaplectic_prefix_support {r : Eisenstein}
    (S : Finset (MetaplecticRetainedCode r))
    (hS : ∀ z ∈ S, ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) :
    ∀ p ∈ S.image metaplecticCodePrefix, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
  exact hS z hz

end CubicFirstMoment

end

end OAI
