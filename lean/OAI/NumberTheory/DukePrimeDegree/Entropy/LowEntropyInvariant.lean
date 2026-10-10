import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereAtomicSupport

namespace OAI

/-!
# Unconditional low-entropy root invariance

For the integer-lattice quotient, a nontrivial distinguished root leaf
and atomic companion leaves force invariance under the distinguished
root subgroup. All support, recurrence, and shearing steps are proved.
This is the low-entropy alternative in EKL (2006), Theorem 2.3, specialized
to the quotient used by the prime-degree packet theorem.
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem root_invariant_of_atomic_companion_leaves
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (hrow : ∀ (k : Fin (d + 1)) (hki : k ≠ i), k ≠ j →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hki.symm μ x = Measure.dirac 0)
    (hcol : ∀ k : Fin (d + 1), k ≠ i → (hkj : k ≠ j) →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hkj μ x = Measure.dirac 0) :
    ∀ a : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨N, hN, hNzero, hs⟩ := exists_nullset_horospherical_root_support d hij μ hA hrow hcol
  apply root_invariant_of_horospherical_root_support d hd hij μ hnontrivial N hN hNzero
  intro x hx g hg hy
  exact ⟨g.val i j, congrArg (rightAction x) (hs x hx g hg hy)⟩

end DukePrimeDegree

end

end OAI
