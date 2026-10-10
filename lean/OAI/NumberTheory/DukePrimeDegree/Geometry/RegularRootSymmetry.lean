import OAI.NumberTheory.DukePrimeDegree.Geometry.RegularRootInvariance
import OAI.NumberTheory.DukePrimeDegree.Dynamics.PrimeSingleBlockHaar

namespace OAI

/-!
# Finite regular entropy tests and prime-degree rigidity

The finite regular entropy identities balance incoming and outgoing root
coefficients. This makes the invariant-root relation symmetric, yielding
Haar classification in prime degree when regular entropy is positive.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The finite family of entropy identities used by the prime-degree
application.  Both time directions are retained explicitly. -/
def CanonicalRegularEntropyTests (d : ℕ) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ a : Option (Fin (d + 1)),
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) =
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) =
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
          (fun i => -regularEntropyTest d a i))

section Measure

variable {d : ℕ} {μ : Measure (X (d + 1))} [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]

/-- Balance of mean root information yields equality of opposite
coefficients, using root invariance and the root commutator. -/
theorem canonicalRootCoefficient_symmetric_of_balance (hd : 2 < d + 1)
    (hbalance : ∀ i, ∑ j, canonicalRootCoefficient d μ i j =
      ∑ j, canonicalRootCoefficient d μ j i) :
    ∀ i j, canonicalRootCoefficient d μ i j = canonicalRootCoefficient d μ j i := by
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  apply coefficients_symmetric_of_balanced_two_step _
    (canonicalRootCoefficient_nonneg d μ) hbalance
  intro a b c hac hab hbc
  have hab' : a ≠ b := by
    rintro rfl
    simp only [canonicalRootCoefficient_diagonal, lt_self_iff_false] at hab
  have hbc' : b ≠ c := by
    rintro rfl
    simp only [canonicalRootCoefficient_diagonal, lt_self_iff_false] at hbc
  have hrab := (rootInvarianceRelation_iff_full_root hab' μ).mpr
    (canonical_root_invariant_of_balance hd hbalance hab' hab)
  have hrbc := (rootInvarianceRelation_iff_full_root hbc' μ).mpr
    (canonical_root_invariant_of_balance hd hbalance hbc' hbc)
  exact canonicalRootCoefficient_one_of_invariant d μ hA a c hac
    ((rootInvarianceRelation_iff_full_root hac μ).mp
      (rootInvarianceRelation_trans μ hrab hrbc))

/-- The actual full-root invariance relation is symmetric under balance
of the actual mean coefficients.  No finite-orbit hypothesis is needed. -/
theorem rootInvarianceRelation_symmetric_of_coefficient_balance (hd : 2 < d + 1)
    (hbalance : ∀ i, ∑ j, canonicalRootCoefficient d μ i j =
      ∑ j, canonicalRootCoefficient d μ j i) :
    Std.Symm (rootInvarianceRelation μ) := by
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hsym := canonicalRootCoefficient_symmetric_of_balance hd hbalance
  constructor
  intro i j hij
  by_cases he : i = j
  · subst j
    exact Or.inl rfl
  have hc : canonicalRootCoefficient d μ i j = 1 :=
    canonicalRootCoefficient_one_of_invariant d μ hA i j he
      ((rootInvarianceRelation_iff_full_root he μ).mp hij)
  have hp : 0 < canonicalRootCoefficient d μ j i := by
    rw [← hsym i j, hc]
    norm_num
  exact (rootInvarianceRelation_iff_full_root (Ne.symm he) μ).mpr
    (canonical_root_invariant_of_balance hd hbalance (Ne.symm he) hp)

/-- Time reversal of only the displayed finite regular entropy tests
supplies the coefficient balance required for actual root symmetry. -/
theorem rootInvarianceRelation_symmetric_of_regular_tests (hd : 2 < d + 1)
    (htests : CanonicalRegularEntropyTests d μ) :
    Std.Symm (rootInvarianceRelation μ) := by
  apply rootInvarianceRelation_symmetric_of_coefficient_balance hd
  exact balanced_of_regular_diagonal_entropy_tests d μ
    (fun u => (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq)
    (canonicalRootCoefficient d μ) (canonicalRootCoefficient_nonneg d μ) htests

/-- Finite regular entropy identities and positive regular entropy give
Haar probability. -/
theorem isHaar_of_prime_regular_entropy_tests
    (hprime : (d + 1).Prime) (hd : 2 < d + 1)
    (htests : CanonicalRegularEntropyTests d μ)
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    IsHaarProbability μ := by
  obtain ⟨i, j, hij, hroot⟩ :=
    exists_invariant_root_of_positive_regular_entropy d hd μ hpos
  apply isHaar_of_prime_symmetric_invariant_roots d hprime μ
    (rootInvarianceRelation_symmetric_of_regular_tests hd htests)
  exact ⟨i, j, hij, (rootInvarianceRelation_iff_full_root hij μ).mpr hroot⟩

end Measure

/-- Finite regular entropy identities for diagonal-ergodic probabilities
imply the prime-degree rigidity criterion. -/
theorem eklPrimeInput_of_regular_entropy_tests (d : ℕ)
    (htests : ∀ (μ : Measure (X (d + 1))) (hμ : IsProbabilityMeasure μ),
      ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ →
        @CanonicalRegularEntropyTests d μ hμ) :
    EKLPrimeInput d := by
  intro hprime hthree μ hμ hμerg hpos
  let : IsProbabilityMeasure μ := hμ
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ := hμerg
  exact isHaar_of_prime_regular_entropy_tests hprime (by omega)
    (htests μ hμ hμerg) hpos

end DukePrimeDegree

end

end OAI
