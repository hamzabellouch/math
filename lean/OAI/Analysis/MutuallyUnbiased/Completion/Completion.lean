import OAI.Analysis.MutuallyUnbiased.Completion.BasisFrame
import OAI.Analysis.MutuallyUnbiased.Completion.ProjectionBasis

namespace OAI

/-!
# Weiner completion in dimension six

The missing orthonormal basis is obtained by simultaneously diagonalizing the
commutative fixed space of the complementary Hilbert--Schmidt projection.
-/

namespace MUB6.Weiner

open Matrix
open scoped BigOperators

lemma unbiased_of_complement_fixed (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B)
    (b : MUB6.Basis)
    (hfixed : ∀ j, applySuper (complementMatrix (fun r => basisCoordinates (B r)))
      (projector (b j)) = projector (b j)) :
    ∀ r i j, Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6 := by
  intro r i j
  have hv : complementMatrix (fun r => basisCoordinates (B r)) *ᵥ
      projectorVector (basisCoordinates b j) = projectorVector (basisCoordinates b j) := by
    funext p
    exact congrArg (fun X : CMatrix => X p.1 p.2) (hfixed j)
  have h := dotProduct_fixed_of_image
    (complementMatrix (fun r => basisCoordinates (B r))) (complementMatrix_hermitian _)
    (projectorVector (basisCoordinates (B r) i)) (projectorVector (basisCoordinates b j))
    traceVector (1 / 6 : ℂ) (basis_complement_projectorVector B hB r i) hv
  rw [basis_projector_inner, traceVector_dot_projectorVector, Complex.star_def,
    Complex.mul_conj] at h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact hre

/-- Every family of six mutually unbiased orthonormal bases of `ℂ⁶` has a
seventh orthonormal basis unbiased to each of them. -/
theorem exists_unbiased_basis (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    ∃ b : MUB6.Basis, ∀ r i j,
      Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6 := by
  have h : ∃ b : MUB6.Basis, ∀ j,
      applySuper (complementMatrix (fun r => basisCoordinates (B r)))
        (projector (b j)) = projector (b j) := by
    have h₀ := exists_fixed_projection_basis (complementMatrix (fun r => basisCoordinates (B r)))
      (complementMatrix_hermitian _) (basis_complement_idempotent B hB)
      (complementMatrix_realigned _) (basis_complement_unital B)
    have hcard : Fintype.card Coord = 6 := Fintype.card_fin 6
    rw [hcard] at h₀
    exact h₀
  obtain ⟨b, hb⟩ := h
  exact ⟨b, unbiased_of_complement_fixed B hB b hb⟩

/-- Append the basis supplied by the completion theorem. -/
noncomputable def appendBasis (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) :
    Fin 7 → MUB6.Basis := Fin.lastCases b B

lemma appendBasis_castSucc (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) (r : Fin 6) :
    appendBasis B b r.castSucc = B r := by simp [appendBasis]

lemma appendBasis_last (B : Fin 6 → MUB6.Basis) (b : MUB6.Basis) :
    appendBasis B b (Fin.last 6) = b :=
  Fin.lastCases_last

lemma appendBasis_isMUB (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) (b : MUB6.Basis)
    (hb : ∀ r i j, Complex.normSq (inner ℂ (B r i) (b j)) = (1 : ℝ) / 6) :
    IsMUBFamily (appendBasis B b) := by
  unfold IsMUBFamily
  intro r
  refine Fin.lastCases ?_ ?_ r
  · intro s
    refine Fin.lastCases ?_ ?_ s
    · intro hrs
      exact (hrs rfl).elim
    · intro s _ i j
      rw [appendBasis_last, appendBasis_castSucc, ← inner_conj_symm]
      simpa only [Complex.normSq_conj] using hb s j i
  · intro r s
    refine Fin.lastCases ?_ ?_ s
    · intro _ i j
      simpa only [appendBasis_castSucc, appendBasis_last] using hb r i j
    · intro s hrs i j
      have hne : r ≠ s := fun h => hrs (congrArg Fin.castSucc h)
      simpa only [appendBasis_castSucc] using hB r s hne i j

/-- Weiner's completion theorem, specialized to six-dimensional complex
Hilbert space, with the original six bases retained at their original indices. -/
theorem six_extend_to_seven (B : Fin 6 → MUB6.Basis) (hB : IsMUBFamily B) :
    ∃ C : Fin 7 → MUB6.Basis, IsMUBFamily C ∧ ∀ r, C r.castSucc = B r := by
  obtain ⟨b, hb⟩ := exists_unbiased_basis B hB
  exact ⟨appendBasis B b, appendBasis_isMUB B hB b hb, appendBasis_castSucc B b⟩

end MUB6.Weiner

end OAI
