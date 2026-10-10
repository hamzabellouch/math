import OAI.NumberTheory.DukePrimeDegree.Geometry.RootSourceOrder
import OAI.NumberTheory.DukePrimeDegree.Geometry.CommutatorInvariance
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyInvariant

namespace OAI

/-! # Without invariant roots the positive-root graph has no two-step path -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma positive_coefficient_atomless (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {i j : Fin (d+1)} (hij : i ≠ j) (hp : 0 < canonicalRootCoefficient d μ i j) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  rcases intrinsicRootLeaf_ergodic_alternative d hij μ with h | h
  · exact h
  · have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    exact (hp.ne' ((canonicalRootCoefficient_zero_iff d μ hA i j hij).mpr h)).elim

/-- The commutator argument handles distinct endpoints; the isolated
opposite-root pair is handled by the already proved low-entropy theorem. -/
theorem no_two_step_positive_roots_of_no_invariant_root (d : ℕ) (hd : 2 < d+1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hnone : ∀ (i j : Fin (d+1)) (hij : i ≠ j), ¬ ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t))=μ) :
    ∀ a b c : Fin (d+1), 0 < canonicalRootCoefficient d μ a b →
      0 < canonicalRootCoefficient d μ b c → False := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hdistinct {i j : Fin (d+1)} (h : 0 < canonicalRootCoefficient d μ i j) : i ≠ j := by
    rintro rfl
    simp only [canonicalRootCoefficient_diagonal,lt_self_iff_false] at h
  have hno {a b c : Fin (d+1)} (hac : a ≠ c)
      (hab : 0 < canonicalRootCoefficient d μ a b)
      (hbc : 0 < canonicalRootCoefficient d μ b c) : False :=
    hnone a c hac (root_invariant_of_adjacent_nonatomic_leaves d
      (hdistinct hab) (hdistinct hbc) hac μ
      (positive_coefficient_atomless d μ (hdistinct hab) hab)
      (positive_coefficient_atomless d μ (hdistinct hbc) hbc))
  intro a b c hab hbc
  by_cases hac : a=c
  · subst c
    have hab' := hdistinct hab
    apply hnone a b hab'
    apply root_invariant_of_atomic_companion_leaves d hd hab' μ
    · filter_upwards [positive_coefficient_atomless d μ hab' hab] with x hx
      let : NullSingletonClass (intrinsicRootLeaf hab' μ x) := hx
      intro he
      have hz := measure_singleton (μ := intrinsicRootLeaf hab' μ x) (0:ℝ)
      simp [he] at hz
    · intro k hka hkb
      apply (canonicalRootCoefficient_zero_iff d μ hA a k hka.symm).mp
      exact le_antisymm (le_of_not_gt fun hp => hno hkb.symm hbc hp)
        (canonicalRootCoefficient_nonneg d μ a k)
    · intro k hka hkb
      apply (canonicalRootCoefficient_zero_iff d μ hA k b hkb).mp
      exact le_antisymm (le_of_not_gt fun hp => hno hka hp hbc)
        (canonicalRootCoefficient_nonneg d μ k b)
  · exact hno hac hab hbc

end DukePrimeDegree

end

end OAI
