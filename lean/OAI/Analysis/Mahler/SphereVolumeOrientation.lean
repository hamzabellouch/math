import OAI.Analysis.Mahler.SphereFluxIntegral

namespace OAI

open Complex

namespace Mahler

/-- The cofactor frame is the actual interleaved real orthonormal coordinate
frame, with the same index equivalence used for the volume form. -/
lemma sphereFrame_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sphereFrame k (ambientFinEquiv k s) = interleavedBasis s := by
  simp only [sphereFrame, OrthonormalBasis.reindex_apply,
    Pi.orthonormalBasis_apply]
  obtain ⟨j,α,h⟩ : ∃ j α, pairSlotEquiv (k+1) s = (j,α) := ⟨_,_,rfl⟩
  fin_cases α <;> simp [interleavedBasis, h, Complex.coe_orthonormalBasisOneI]

/-- The volume form evaluates to +1 on a real orthonormal frame.
This verifies its Euclidean metric normalization as well as its sign. -/
theorem sphereVolume_orthonormalFrame (k : ℕ) : sphereVolume k (sphereFrame k) = 1 := by
  rw [sphereVolume, AlternatingMap.domDomCongr_apply]
  have he : sphereFrame k ∘ ambientFinEquiv k = interleavedBasis :=
    funext (sphereFrame_interleaved k)
  rw [he, interleavedVolume_basis]

end Mahler

end OAI
