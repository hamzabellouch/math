import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase

namespace OAI

/-!
# Invariant roots have nonatomic conditional measures

The pointwise atomic transversal is incompatible with any fixed nonzero
measure-preserving root translation. Diagonal ergodicity then selects
the nonatomic branch of the intrinsic leaf alternative.
-/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem not_ae_dirac_of_root_invariant
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij 1)) = μ) :
    ¬ (∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0) := by
  intro hatom
  obtain ⟨N, hN, hz, hsep⟩ := exists_nullset_atomic_root_transversal d hij μ hA hatom
  have hae : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hz
  have hpre : ∀ᵐ x ∂μ, rightAction x
      (Matrix.SpecialLinearGroup.transvection hij 1) ∉ N := by
    have hm : ∀ᵐ y ∂μ.map (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij 1)), y ∉ N := by
      rwa [hinv]
    exact ae_of_ae_map (continuous_rightAction
      (Matrix.SpecialLinearGroup.transvection hij 1)).measurable.aemeasurable hm
  obtain ⟨x, hx, htx⟩ := (hae.and hpre).exists
  exact one_ne_zero (hsep x hx 1 htx)

theorem ae_nonatomic_of_root_invariant
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij 1)) = μ) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  exact (intrinsicRootLeaf_ergodic_alternative d hij μ).resolve_right
    (not_ae_dirac_of_root_invariant d hij μ hA hinv)

end DukePrimeDegree

end

end OAI
