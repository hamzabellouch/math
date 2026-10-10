import OAI.Analysis.PlanarPacking.FiniteCoordinates
import OAI.Analysis.PlanarPacking.Indices

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteProjection_apply (x : X) (k : Node × Bool) :
    finiteEmbedding e (finiteRestriction e he x) k = if ∃ i, e i=k then x k else 0 := by
  classical
  rw [finiteEmbedding_apply]
  split_ifs with h
  · obtain ⟨i,rfl⟩ := h
    simp only [he.eq_iff, finiteRestriction_apply]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => h ⟨i,hh⟩)]
end
end SharpPlanar

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable abbrev RJ := finiteRestriction centralIndex centralIndex_injective
noncomputable abbrev IJ := finiteEmbedding centralIndex
noncomputable abbrev RE := finiteRestriction exteriorIndex exteriorIndex_injective
noncomputable abbrev IE := finiteEmbedding exteriorIndex
noncomputable abbrev RF := finiteRestriction finiteIndex finiteIndex_injective
noncomputable abbrev IF := finiteEmbedding finiteIndex
noncomputable abbrev RL := finiteRestriction lowExteriorIndex lowExteriorIndex_injective
noncomputable abbrev IL := finiteEmbedding lowExteriorIndex
end SharpPlanar.Numerical

end OAI
