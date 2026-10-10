import OAI.NumberTheory.JointDickman.Counting.CoefficientRegularityLoss
import OAI.NumberTheory.JointDickman.Counting.CoefficientTripleBound

namespace OAI

/-! # Exact sign reversal for the coefficient relation a - b = jc -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def coefficientRelationWeight (B : ℕ) (j : ℤ) (a b c : ℕ) : ℝ :=
  if (a : ℤ) = b + j * c then
    coefficientWeight B a * coefficientWeight B b * coefficientWeight B c else 0

noncomputable def signedCoefficientMass (B : ℕ) (j : ℤ) (I J : Finset ℕ) : ℝ :=
  ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ J, coefficientRelationWeight B j a b c

theorem coefficientRelationWeight_neg (B : ℕ) (j : ℤ) (a b c : ℕ) :
    coefficientRelationWeight B (-j) a b c = coefficientRelationWeight B j b a c := by
  have hh : ((a : ℤ) = b + -j * c) ↔ ((b : ℤ) = a + j * c) := by constructor <;> intro h <;> linarith
  unfold coefficientRelationWeight
  simp only [hh]
  split_ifs <;> ring

theorem signedCoefficientMass_neg (B : ℕ) (j : ℤ) (I J : Finset ℕ) :
    signedCoefficientMass B (-j) I J = signedCoefficientMass B j I J := by
  unfold signedCoefficientMass
  simp_rw [coefficientRelationWeight_neg]
  exact sum_comm

theorem coefficientRelationWeight_nat (B j a b c : ℕ) :
    coefficientRelationWeight B (j : ℤ) a b c =
      if a = b + j * c then tripleCoefficientWeight B j b c else 0 := by
  have hh : ((a : ℤ) = b + (j : ℤ) * c) ↔ a = b + j * c := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj]
  unfold coefficientRelationWeight
  simp only [hh]
  split_ifs with h
  · rw [h]
    unfold tripleCoefficientWeight
    ring
  · rfl

theorem signedCoefficientMass_nat_le (B j : ℕ) (I J : Finset ℕ) :
    signedCoefficientMass B (j : ℤ) I J ≤
      ∑ b ∈ I, ∑ c ∈ J, tripleCoefficientWeight B j b c := by
  classical
  unfold signedCoefficientMass
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [sum_comm]
  apply sum_le_sum
  intro c _
  simp_rw [coefficientRelationWeight_nat]
  rw [sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact tripleCoefficientWeight_nonneg B j b c

/-- Both signs of the lag satisfy the same rectangle bound, including the
support restriction that both a and b belong to the coefficient interval. -/
theorem signed_coefficient_three_form_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℤ) (u v w x : ℕ),
      j ≠ 0 → u ≤ v → w ≤ x →
      Real.exp (δ * B) ≤ (v : ℝ) - u → Real.exp (δ * B) ≤ (x : ℝ) - w →
      signedCoefficientMass B j (Ico u v) (Ico w x) ≤
        C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j.natAbs := by
  obtain ⟨C, hC, hbound⟩ := coefficient_three_form_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hB
  intro j u v w x hj huv hwx hL hH
  have hnat : j.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hj
  have hh := (signedCoefficientMass_nat_le B j.natAbs (Ico u v) (Ico w x)).trans
    (hB j.natAbs u v w x hnat huv hwx hL hH)
  rcases Int.natAbs_eq j with hsign | hsign
  · simpa only [← hsign] using hh
  · rw [hsign, signedCoefficientMass_neg]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hh

end JointDickman

end OAI
