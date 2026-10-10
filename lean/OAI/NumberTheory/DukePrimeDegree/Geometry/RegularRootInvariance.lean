import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic
import OAI.NumberTheory.DukePrimeDegree.Geometry.CommutatorInvariance
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyInvariant
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularEntropyTests
import OAI.NumberTheory.DukePrimeDegree.Entropy.RegularEntropyScaling

namespace OAI

/-! # Root invariance from the finite regular entropy tests

The prime-degree application needs balance and one positive coefficient.
The symmetry argument below uses only the explicit regular test weights,
not an entropy formula at arbitrary or singular weights.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {d : ℕ} {μ : Measure (X (d+1))} [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]

private lemma canonical_atomless_of_pos {i j : Fin (d+1)} (hij : i ≠ j)
    (hpos : 0 < canonicalRootCoefficient d μ i j) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  rcases intrinsicRootLeaf_ergodic_alternative d hij μ with h | h
  · exact h
  · have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    exact (hpos.ne' ((canonicalRootCoefficient_zero_iff d μ hA i j hij).mpr h)).elim

private lemma canonical_two_step (a b c : Fin (d+1)) (hac : a ≠ c)
    (hab : 0 < canonicalRootCoefficient d μ a b)
    (hbc : 0 < canonicalRootCoefficient d μ b c) :
    canonicalRootCoefficient d μ a c = 1 := by
  have hab' : a ≠ b := by
    intro h; subst b
    simp only [canonicalRootCoefficient_diagonal, lt_self_iff_false] at hab
  have hbc' : b ≠ c := by
    intro h; subst c
    simp only [canonicalRootCoefficient_diagonal, lt_self_iff_false] at hbc
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  exact canonicalRootCoefficient_one_of_invariant d μ hA a c hac
    (root_invariant_of_adjacent_nonatomic_leaves d hab' hbc' hac μ
      (canonical_atomless_of_pos hab' hab) (canonical_atomless_of_pos hbc' hbc))

/-- Actual root invariance follows from coefficient balance, using the
proved commutator and isolated-root shearing alternatives. -/
theorem canonical_root_invariant_of_balance (hd : 2 < d+1)
    (hbalance : ∀ i, ∑ j, canonicalRootCoefficient d μ i j =
      ∑ j, canonicalRootCoefficient d μ j i)
    {i j : Fin (d+1)} (hij : i ≠ j)
    (hpos : 0 < canonicalRootCoefficient d μ i j) :
    ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hsym : ∀ a b, canonicalRootCoefficient d μ a b = canonicalRootCoefficient d μ b a :=
    coefficients_symmetric_of_balanced_two_step _
      (canonicalRootCoefficient_nonneg d μ) hbalance canonical_two_step
  by_cases hr : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < canonicalRootCoefficient d μ i k
  · obtain ⟨k,hki,hkj,hik⟩ := hr
    have hki' : 0 < canonicalRootCoefficient d μ k i := by rwa [hsym k i]
    have hkjInv := root_invariant_of_adjacent_nonatomic_leaves d hki hij hkj μ
      (canonical_atomless_of_pos hki hki') (canonical_atomless_of_pos hij hpos)
    have hkj' : 0 < canonicalRootCoefficient d μ k j := by
      rw [canonicalRootCoefficient_one_of_invariant d μ hA k j hkj hkjInv]
      norm_num
    exact root_invariant_of_adjacent_nonatomic_leaves d hki.symm hkj hij μ
      (canonical_atomless_of_pos hki.symm hik) (canonical_atomless_of_pos hkj hkj')
  by_cases hc : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < canonicalRootCoefficient d μ k j
  · obtain ⟨k,hki,hkj,hkj'⟩ := hc
    have hjk : 0 < canonicalRootCoefficient d μ j k := by rwa [hsym j k]
    have hikInv := root_invariant_of_adjacent_nonatomic_leaves d hij hkj.symm hki.symm μ
      (canonical_atomless_of_pos hij hpos) (canonical_atomless_of_pos hkj.symm hjk)
    have hik : 0 < canonicalRootCoefficient d μ i k := by
      rw [canonicalRootCoefficient_one_of_invariant d μ hA i k hki.symm hikInv]
      norm_num
    exact root_invariant_of_adjacent_nonatomic_leaves d hki.symm hkj hij μ
      (canonical_atomless_of_pos hki.symm hik) (canonical_atomless_of_pos hkj hkj')
  apply root_invariant_of_atomic_companion_leaves d hd hij μ
  · filter_upwards [canonical_atomless_of_pos hij hpos] with x hx
    let : NullSingletonClass (intrinsicRootLeaf hij μ x) := hx
    intro he
    have hz := measure_singleton (μ := intrinsicRootLeaf hij μ x) (0 : ℝ)
    simp [he] at hz
  · intro k hki hkj
    apply (canonicalRootCoefficient_zero_iff d μ hA i k hki.symm).mp
    exact le_antisymm (le_of_not_gt fun hp => hr ⟨k,hki,hkj,hp⟩)
      (canonicalRootCoefficient_nonneg d μ i k)
  · intro k hki hkj
    apply (canonicalRootCoefficient_zero_iff d μ hA k j hkj).mp
    exact le_antisymm (le_of_not_gt fun hp => hc ⟨k,hki,hkj,hp⟩)
      (canonicalRootCoefficient_nonneg d μ k j)

/-- Only the finite family of regular entropy identities is needed to
turn any positive actual coefficient into ambient root invariance. -/
theorem canonical_root_invariant_of_regular_tests (hd : 2 < d+1)
    (htests : ∀ a : Option (Fin (d+1)),
      measureEntropy μ (fun x => rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) =
          ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
      measureEntropy μ (fun x => rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) =
          ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
            (fun i => -regularEntropyTest d a i)))
    {i j : Fin (d+1)} (hij : i ≠ j) (hpos : 0 < canonicalRootCoefficient d μ i j) :
    ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ := by
  apply canonical_root_invariant_of_balance hd _ hij hpos
  exact balanced_of_regular_diagonal_entropy_tests d μ
    (fun u => (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq)
    (canonicalRootCoefficient d μ) (canonicalRootCoefficient_nonneg d μ) htests

/-- Positive entropy for the original regular diagonal map supplies an
actual invariant root subgroup once the finite regular test identities
have been identified. No formula at singular weights is used. -/
theorem exists_invariant_root_of_regular_tests (hd : 2 < d+1)
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)))
    (htests : ∀ a : Option (Fin (d+1)),
      measureEntropy μ (fun x => rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) =
          ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
      measureEntropy μ (fun x => rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) =
          ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
            (fun i => -regularEntropyTest d a i))) :
    ∃ (i j : Fin (d+1)) (hij : i ≠ j), ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ := by
  have hp := positive_entropy_regular_test d μ
    (fun u => (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq) hpos
  rw [(htests none).1, ENNReal.ofReal_pos] at hp
  have hex : ∃ i j : Fin (d+1), i ≠ j ∧ 0 < canonicalRootCoefficient d μ i j := by
    by_contra! hn
    have hz : ∀ i j, canonicalRootCoefficient d μ i j = 0 := by
      intro i j
      by_cases hij : i = j
      · subst j
        exact canonicalRootCoefficient_diagonal d μ i
      · exact le_antisymm (hn i j hij) (canonicalRootCoefficient_nonneg d μ i j)
    simp only [rootEntropyForm, hz, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hp
  obtain ⟨i,j,hij,hijpos⟩ := hex
  exact ⟨i,j,hij,canonical_root_invariant_of_regular_tests hd htests hij hijpos⟩

end DukePrimeDegree

end

end OAI
