import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeFacetTemplate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightSamplingPolytope
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponents

namespace OAI

/-! # Exact positive widths of the sampling polytope -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- Every defining halfspace is attained at its Euclidean contact point. -/
theorem weightSampling_support_eq_norm
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hC : IsCompact (weightSamplingPolytope α))
    (i : I) (hi : α i ≠ 0) :
    sSup (α i '' weightSamplingPolytope α) = ‖α i‖ := by
  obtain ⟨p, hp, hval, _⟩ := exists_weight_contact_point (α i) hi
  have hpC : p ∈ weightSamplingPolytope α :=
    closedBall_subset_weightSamplingPolytope α (by simpa using hp.le)
  apply le_antisymm
  · have himg : (α i '' weightSamplingPolytope α).Nonempty := ⟨α i p, p, hpC, rfl⟩
    apply csSup_le himg
    rintro _ ⟨x, hx, rfl⟩
    exact hx i
  · rw [← hval]
    exact le_csSup (hC.image (α i).continuous).bddAbove ⟨p, hpC, rfl⟩

/-- Every nonempty bracket word has strictly positive sampling width. -/
theorem bracketWordExponent_pos
    {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (hs : ∀ i, 0 < s i) (w : FreeMagma I) :
    0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa using hs i
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    simpa only [bracketWordExponent_mul] using add_pos hu hv

end PolycyclicRecognition

end

end OAI
