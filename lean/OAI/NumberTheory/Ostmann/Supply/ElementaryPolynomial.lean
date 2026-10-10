import OAI.NumberTheory.Ostmann.Characters.PolynomialCircleEstimate

namespace OAI

/-! # The subset polynomial used in the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def elementaryCoefficient {n : ℕ} (b : Fin n → ℂ) (j : ℕ) : ℂ :=
  ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j), ∏ i ∈ I, b i

theorem elementaryCoefficient_polynomial {n : ℕ} (b : Fin n → ℂ) (u : ℂ) :
    finitePolynomial (elementaryCoefficient b) (n + 1) u = ∏ i, (1 + u * b i) := by
  unfold finitePolynomial elementaryCoefficient
  simp_rw [smul_eq_mul, Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j),
          u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro I hI
      rw [(Finset.mem_filter.mp hI).2]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_fiberwise_of_maps_to
      intro I hI
      apply Finset.mem_range.mpr
      have hh := Finset.card_le_card (Finset.mem_powerset.mp hI)
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le hh
    _ = _ := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem elementaryCoefficient_product {n : ℕ} (b : Fin n → ℂ) (u v : ℂ) :
    finitePolynomial₂ (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) u v = (∏ i, (1 + u * b i)) * ∏ i, (1 + v * b i) := by
  rw [← elementaryCoefficient_polynomial b u, ← elementaryCoefficient_polynomial b v]
  unfold finitePolynomial₂ finitePolynomial
  simp only [smul_eq_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def elementaryTruncation {n : ℕ} (b : Fin n → ℂ) (K : ℕ) : ℂ :=
  ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card ≤ K), ∏ i ∈ I, b i

theorem elementaryTruncation_eq {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    (∑ i ∈ Finset.range (n + 1), if i ≤ K then elementaryCoefficient b i else 0) =
      elementaryTruncation b K := by
  rw [← Finset.sum_filter]
  unfold elementaryCoefficient elementaryTruncation
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨hI, _, hK⟩
      exact ⟨hI, hK⟩
    · rintro ⟨hI, hK⟩
      have hh : I.card ≤ n := by simpa using Finset.card_le_card hI
      exact ⟨hI, Nat.lt_succ_of_le hh, hK⟩
  · intro I _
    rfl

theorem elementaryTruncation_square {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    rectangularPolynomialSum (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) K = elementaryTruncation b K ^ 2 := by
  rw [pow_two, ← elementaryTruncation_eq b K]
  unfold rectangularPolynomialSum
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ≤ K <;> by_cases hj : j ≤ K <;> simp [hi, hj]

end Ostmann

end OAI
