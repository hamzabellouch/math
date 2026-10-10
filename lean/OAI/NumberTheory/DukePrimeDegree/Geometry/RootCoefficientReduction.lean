import OAI.NumberTheory.DukePrimeDegree.Geometry.CommutatorInvariance
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyInvariant
import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalEntropy

namespace OAI

/-!
# The entropy formula and invariant root blocks

The root coefficients satisfy the entropy formula, zero criterion and
Haar normalization of EKL (2006), Proposition 3.1. The commutator and
shearing arguments give invariance in the high- and low-entropy cases.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Root entropy coefficients as in EKL (2006), Proposition 3.1,
with zero diagonal. -/
structure RootEntropyCoefficients (d : ℕ) (μ : Measure (X (d + 1)))
    [IsFiniteMeasure μ] where
  coefficient : Fin (d + 1) → Fin (d + 1) → ℝ
  diagonal_zero : ∀ i, coefficient i i = 0
  nonneg : ∀ i j, 0 ≤ coefficient i j
  zero_iff : ∀ i j (hij : i ≠ j), coefficient i j = 0 ↔
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0
  one_of_invariant : ∀ i j (hij : i ≠ j),
    (∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ) → coefficient i j = 1
  entropy_formula : ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0),
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) =
      ENNReal.ofReal (rootEntropyForm coefficient ell)

namespace RootEntropyCoefficients

variable {d : ℕ} {μ : Measure (X (d + 1))} [IsProbabilityMeasure μ]
  [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
  (C : RootEntropyCoefficients d μ)

lemma atomless_of_pos {i j : Fin (d + 1)} (hij : i ≠ j)
    (hpos : 0 < C.coefficient i j) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  rcases intrinsicRootLeaf_ergodic_alternative d hij μ with h | h
  · exact h
  · exact (hpos.ne' ((C.zero_iff i j hij).mpr h)).elim

lemma nontrivial_of_pos {i j : Fin (d + 1)} (hij : i ≠ j)
    (hpos : 0 < C.coefficient i j) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0 := by
  filter_upwards [C.atomless_of_pos hij hpos] with x hx
  let : NullSingletonClass (intrinsicRootLeaf hij μ x) := hx
  intro he
  have hzero := measure_singleton (μ := intrinsicRootLeaf hij μ x) (0 : ℝ)
  simp [he] at hzero

lemma balanced : ∀ i, ∑ j, C.coefficient i j = ∑ j, C.coefficient j i := by
  apply balanced_of_diagonal_entropy_formula d μ _ C.coefficient C.nonneg C.entropy_formula
  intro u
  exact (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq

lemma two_step (a b c : Fin (d + 1)) (hac : a ≠ c)
    (hab : 0 < C.coefficient a b) (hbc : 0 < C.coefficient b c) :
    C.coefficient a c = 1 := by
  have hab' : a ≠ b := by
    intro h
    subst b
    simp only [C.diagonal_zero, lt_self_iff_false] at hab
  have hbc' : b ≠ c := by
    intro h
    subst c
    simp only [C.diagonal_zero, lt_self_iff_false] at hbc
  exact C.one_of_invariant a c hac (root_invariant_of_adjacent_nonatomic_leaves d
    hab' hbc' hac μ (C.atomless_of_pos hab' hab) (C.atomless_of_pos hbc' hbc))

lemma symmetric : ∀ i j, C.coefficient i j = C.coefficient j i :=
  coefficients_symmetric_of_balanced_two_step C.coefficient C.nonneg C.balanced C.two_step

/-- The high-entropy case: a third positive coefficient in the same row
forces invariance. The two applications of the commutator theorem are
explicit, so no converse to the Haar normalization is required. -/
lemma invariant_of_positive_row {a b c : Fin (d + 1)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hposab : 0 < C.coefficient a b) (hposac : 0 < C.coefficient a c) :
    ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hab t)) = μ := by
  have hposca : 0 < C.coefficient c a := by rwa [C.symmetric c a]
  have hcb := root_invariant_of_adjacent_nonatomic_leaves d hac.symm hab hbc.symm μ
    (C.atomless_of_pos hac.symm hposca) (C.atomless_of_pos hab hposab)
  have hposcb : 0 < C.coefficient c b := by
    rw [C.one_of_invariant c b hbc.symm hcb]
    norm_num
  exact root_invariant_of_adjacent_nonatomic_leaves d hac hbc.symm hab μ
    (C.atomless_of_pos hac hposac) (C.atomless_of_pos hbc.symm hposcb)

lemma invariant_of_positive_column {a b c : Fin (d + 1)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hposab : 0 < C.coefficient a b) (hposcb : 0 < C.coefficient c b) :
    ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hab t)) = μ := by
  have hposbc : 0 < C.coefficient b c := by rwa [C.symmetric b c]
  have hacInv := root_invariant_of_adjacent_nonatomic_leaves d hab hbc hac μ
    (C.atomless_of_pos hab hposab) (C.atomless_of_pos hbc hposbc)
  have hposac : 0 < C.coefficient a c := by
    rw [C.one_of_invariant a c hac hacInv]
    norm_num
  exact root_invariant_of_adjacent_nonatomic_leaves d hac hbc.symm hab μ
    (C.atomless_of_pos hac hposac) (C.atomless_of_pos hbc.symm hposcb)

/-- Combining the proved high- and low-entropy cases turns each positive
root coefficient into actual invariance of the ambient measure. -/
theorem invariant_of_pos (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (hpos : 0 < C.coefficient i j) :
    ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ := by
  by_cases hr : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < C.coefficient i k
  · obtain ⟨k, hki, hkj, hp⟩ := hr
    exact C.invariant_of_positive_row hij hki.symm hkj.symm hpos hp
  by_cases hc : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < C.coefficient k j
  · obtain ⟨k, hki, hkj, hp⟩ := hc
    exact C.invariant_of_positive_column hij hki.symm hkj.symm hpos hp
  apply root_invariant_of_atomic_companion_leaves d hd hij μ (C.nontrivial_of_pos hij hpos)
  · intro k hki hkj
    apply (C.zero_iff i k hki.symm).mp
    exact le_antisymm (le_of_not_gt fun hp => hr ⟨k, hki, hkj, hp⟩) (C.nonneg i k)
  · intro k hki hkj
    apply (C.zero_iff k j hkj).mp
    exact le_antisymm (le_of_not_gt fun hp => hc ⟨k, hki, hkj, hp⟩) (C.nonneg k j)

theorem zero_or_one (hd : 2 < d + 1) (i j : Fin (d + 1)) :
    C.coefficient i j = 0 ∨ C.coefficient i j = 1 := by
  by_cases hij : i = j
  · subst j
    exact Or.inl (C.diagonal_zero i)
  by_cases hp : 0 < C.coefficient i j
  · exact Or.inr (C.one_of_invariant i j hij (C.invariant_of_pos hd hij hp))
  · exact Or.inl (le_antisymm (le_of_not_gt hp) (C.nonneg i j))

include C in
/-- Positive entropy supplies a nontrivial invariant root subgroup. -/
theorem exists_invariant_root_of_entropy_pos (hd : 2 < d + 1)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (hpos : 0 < measureEntropy μ
      (fun x => rightAction x (diagonalOneParameter ell hell 1))) :
    ∃ (i j : Fin (d + 1)) (hij : i ≠ j), ∀ t : ℝ,
      μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) = μ := by
  have hform : 0 < rootEntropyForm C.coefficient ell := by
    rw [C.entropy_formula] at hpos
    exact ENNReal.ofReal_pos.mp hpos
  have hex : ∃ i j, 0 < C.coefficient i j := by
    by_contra h
    have hz : ∀ i j, C.coefficient i j = 0 := by
      intro i j
      exact le_antisymm (le_of_not_gt fun hp => h ⟨i, j, hp⟩) (C.nonneg i j)
    simp only [rootEntropyForm, hz, zero_mul, Finset.sum_const_zero] at hform
    exact (lt_irrefl 0 hform)
  obtain ⟨i, j, hp⟩ := hex
  have hij : i ≠ j := by
    intro he
    subst j
    simp only [C.diagonal_zero, lt_self_iff_false] at hp
  exact ⟨i, j, hij, C.invariant_of_pos hd hij hp⟩

end RootEntropyCoefficients
end DukePrimeDegree

end

end OAI
