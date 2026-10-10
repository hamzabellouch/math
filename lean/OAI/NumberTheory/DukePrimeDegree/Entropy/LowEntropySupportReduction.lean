import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyCollision
import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereSeparation

namespace OAI

/-!
# Reduction of root invariance to the published support lemma

For the integer-lattice quotient, exclusion of exceptional neutral
returns and the shearing argument give root invariance from the support
conclusion of EKL (2006), Lemma 4.4(1).
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem root_invariant_of_horospherical_root_support
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (hsupport : ∀ x ∉ N, ∀ h : G (d + 1), RootHorosphereShape i j h →
      rightAction x h ∉ N → ∃ t : ℝ,
        rightAction x h = rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) :
    ∀ a : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  by_contra hnot
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨M, hM, hMzero, hsep⟩ :=
    exists_horospherical_leaf_separation_of_root_support d hij μ hnot N hN hNzero hsupport
  obtain ⟨x, hx, h, hshape, hy, hne, heq⟩ :=
    exists_distinct_equal_leaf_horospherical_pair d hd hij μ hA hnontrivial M hM hMzero
  exact hne (hsep x hx h hshape hy heq)

end DukePrimeDegree

end

end OAI
