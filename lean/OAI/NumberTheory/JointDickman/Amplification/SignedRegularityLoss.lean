import OAI.NumberTheory.JointDickman.Counting.SignedCoefficientSums

namespace OAI

/-! # Regularity loss on the signed coefficient support -/

namespace JointDickman

open Filter Finset
open scoped Topology

def coefficientTripleRegular (B L : ℕ) (τ C : ℝ) (a b c : ℕ) : Prop :=
  RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B b) ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B c)

theorem coefficientTripleRegular_swap (B L : ℕ) (τ C : ℝ) (a b c : ℕ) :
    coefficientTripleRegular B L τ C a b c ↔ coefficientTripleRegular B L τ C b a c := by
  simp only [coefficientTripleRegular, and_left_comm]

theorem coefficientForm_regular_iff (B L j b c : ℕ) (τ C : ℝ) :
    (∀ k : Fin 3, RegularPrimeSet B L τ C (coefficientPrimeSet B (coefficientForm k j b c))) ↔
      coefficientTripleRegular B L τ C (b + j * c) b c := by
  constructor
  · intro h
    exact ⟨by simpa [coefficientForm] using h 2,
      by simpa [coefficientForm] using h 0, by simpa [coefficientForm] using h 1⟩
  · rintro ⟨ha, hb, hc⟩ k
    fin_cases k <;> simpa [coefficientForm] using (by assumption)

open Classical in
noncomputable def discardedRelationWeight (B L : ℕ) (τ C : ℝ) (j : ℤ) (a b c : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else coefficientRelationWeight B j a b c

noncomputable def signedDiscardedCoefficientMass (B L : ℕ) (τ C : ℝ)
    (j : ℤ) (I J : Finset ℕ) : ℝ :=
  ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ J, discardedRelationWeight B L τ C j a b c

theorem discardedRelationWeight_neg (B L : ℕ) (τ C : ℝ) (j : ℤ) (a b c : ℕ) :
    discardedRelationWeight B L τ C (-j) a b c = discardedRelationWeight B L τ C j b a c := by
  by_cases h : coefficientTripleRegular B L τ C a b c
  · have h' := (coefficientTripleRegular_swap B L τ C a b c).mp h
    simp only [discardedRelationWeight, h, h', ite_true]
  · have h' := (coefficientTripleRegular_swap B L τ C a b c).not.mp h
    simp only [discardedRelationWeight, h, h', ite_false, coefficientRelationWeight_neg]

theorem signedDiscardedCoefficientMass_neg (B L : ℕ) (τ C : ℝ) (j : ℤ) (I J : Finset ℕ) :
    signedDiscardedCoefficientMass B L τ C (-j) I J = signedDiscardedCoefficientMass B L τ C j I J := by
  unfold signedDiscardedCoefficientMass
  simp_rw [discardedRelationWeight_neg]
  exact sum_comm

theorem discardedRelationWeight_nat (B L j a b c : ℕ) (τ C : ℝ) :
    discardedRelationWeight B L τ C (j : ℤ) a b c =
      if a = b + j * c then discardedCoefficientWeight B L j b c τ C else 0 := by
  classical
  unfold discardedRelationWeight
  rw [coefficientRelationWeight_nat]
  by_cases h : a = b + j * c
  · subst a
    simp only [ite_true, discardedCoefficientWeight, coefficientForm_regular_iff]
  · simp only [h, ite_false, ite_self]

theorem discardedCoefficientWeight_nonneg (B L j b c : ℕ) (τ C : ℝ) :
    0 ≤ discardedCoefficientWeight B L j b c τ C := by
  unfold discardedCoefficientWeight
  split_ifs
  · rfl
  · exact tripleCoefficientWeight_nonneg ..

theorem signedDiscardedCoefficientMass_nat_le (B L j : ℕ) (τ C : ℝ) (I J : Finset ℕ) :
    signedDiscardedCoefficientMass B L τ C (j : ℤ) I J ≤
      ∑ b ∈ I, ∑ c ∈ J, discardedCoefficientWeight B L j b c τ C := by
  classical
  unfold signedDiscardedCoefficientMass
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [sum_comm]
  apply sum_le_sum
  intro c _
  simp_rw [discardedRelationWeight_nat]
  rw [sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact discardedCoefficientWeight_nonneg ..

/-- Manuscript (9) on the actual signed support a - b = jc. -/
theorem signed_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (j : ℤ) (l₁ r₁ l₂ r₂ : ℕ),
          0 ≤ C → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
          Real.exp (δ * B) ≤ (r₁ : ℝ) - l₁ → Real.exp (δ * B) ≤ (r₂ : ℝ) - l₂ →
          signedDiscardedCoefficientMass B L τ C j (Ico l₁ r₁) (Ico l₂ r₂) ≤
            K * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j.natAbs *
              (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := coefficient_regularity_loss hFord hM hδ hδ32
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent] with B hB
  intro C j l₁ r₁ l₂ r₂ hC hj hI hJ hlen₁ hlen₂
  have hh := (signedDiscardedCoefficientMass_nat_le B L j.natAbs τ C (Ico l₁ r₁) (Ico l₂ r₂)).trans
    (hB C j.natAbs l₁ r₁ l₂ r₂ hC (Int.natAbs_ne_zero.mpr hj) hI hJ hlen₁ hlen₂)
  rcases Int.natAbs_eq j with hsign | hsign
  · simpa only [← hsign] using hh
  · rw [hsign, signedDiscardedCoefficientMass_neg]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hh

end JointDickman

end OAI
