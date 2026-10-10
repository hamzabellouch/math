import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Rat

namespace OAI

noncomputable section
namespace GrahamSpherical

/-- The designated transcendental real is retained in the actual maximal
algebraically independent subset of the real field. -/
theorem exists_real_transcendenceBasis_containing (a : ℝ)
    (ha : Transcendental ℚ a) :
    ∃ B : Set ℝ, a ∈ B ∧ IsTranscendenceBasis ℚ (fun b : B => (b : ℝ)) := by
  have hs : AlgebraicIndepOn ℚ id ({a} : Set ℝ) := by
    exact (algebraicIndependent_singleton_iff
      (R := ℚ) (x := fun b : ({a} : Set ℝ) => (b : ℝ)) ⟨a, by simp⟩).2 ha
  obtain ⟨B, hsub, hB⟩ := exists_isTranscendenceBasis_superset hs
  exact ⟨B, hsub (by simp), hB⟩

end GrahamSpherical

end

end OAI
