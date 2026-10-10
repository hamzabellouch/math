import Mathlib

namespace OAI

namespace FiniteFactor
open Polynomial

theorem product_has_low_nonzero_coeff (K : ℕ) (p q : ℂ[X])
    (hp : p.coeff K ≠ 0) (hq : q.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (p * q).coeff n ≠ 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  refine ⟨(p * q).natTrailingDegree, ?_,
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hp0 hq0)⟩
  rw [Polynomial.natTrailingDegree_mul hp0 hq0]
  have ha := Polynomial.natTrailingDegree_le_of_ne_zero hp
  have hb := Polynomial.natTrailingDegree_le_of_ne_zero hq
  omega

abbrev Coefficients (K : ℕ) := Fin (2 * K + 1) → ℂ

noncomputable def coefficientPolynomial {K : ℕ} (a : Coefficients K) : ℂ[X] :=
  ∑ i : Fin (2 * K + 1), Polynomial.monomial i.val (a i)

theorem coefficientPolynomial_coeff {K : ℕ} (a : Coefficients K)
    (i : Fin (2 * K + 1)) : (coefficientPolynomial a).coeff i.val = a i := by
  classical
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

noncomputable def productCoefficient {K : ℕ} (a b : Coefficients K) (n : ℕ) : ℂ :=
  ∑ i : Fin (2 * K + 1), ∑ j : Fin (2 * K + 1),
    if i.val + j.val = n then a i * b j else 0

theorem productCoefficient_eq {K : ℕ} (a b : Coefficients K) (n : ℕ) :
    productCoefficient a b n =
      (coefficientPolynomial a * coefficientPolynomial b).coeff n := by
  classical
  simp only [productCoefficient, coefficientPolynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  exact Finset.sum_comm

theorem continuous_productCoefficient (K n : ℕ) :
    Continuous (fun ab : Coefficients K × Coefficients K =>
      productCoefficient ab.1 ab.2 n) := by
  classical
  unfold productCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

noncomputable def lowCoefficients {K : ℕ} (ab : Coefficients K × Coefficients K) :
    Coefficients K := fun n => productCoefficient ab.1 ab.2 n.val

theorem continuous_lowCoefficients (K : ℕ) : Continuous (@lowCoefficients K) :=
  continuous_pi fun n => continuous_productCoefficient K n.val

theorem lowCoefficients_ne_zero {K : ℕ} (ab : Coefficients K × Coefficients K)
    (ha : ab.1 ⟨K, by omega⟩ ≠ 0) (hb : ab.2 ⟨K, by omega⟩ ≠ 0) :
    lowCoefficients ab ≠ 0 := by
  have ha' : (coefficientPolynomial ab.1).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.1 ⟨K, by omega⟩).trans_ne ha
  have hb' : (coefficientPolynomial ab.2).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.2 ⟨K, by omega⟩).trans_ne hb
  obtain ⟨n, hn, hne⟩ := product_has_low_nonzero_coeff K _ _ ha' hb'
  intro h
  have hz := congrFun h ⟨n, by omega⟩
  exact hne (by simpa [lowCoefficients, productCoefficient_eq] using hz)

def admissibleCoefficients (K : ℕ) (D δ : ℝ) : Set (Coefficients K) :=
  {a | ∀ i, ‖a i‖ ≤ D} ∩ {a | δ ≤ ‖a ⟨K, by omega⟩‖}

theorem isCompact_admissibleCoefficients (K : ℕ) (D δ : ℝ) :
    IsCompact (admissibleCoefficients K D δ) := by
  have hc : IsCompact {a : Coefficients K | ∀ i, ‖a i‖ ≤ D} := by
    simpa [Set.pi, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite fun _ : Fin (2 * K + 1) =>
        isCompact_closedBall (0 : ℂ) D)
  exact hc.inter_right (isClosed_le continuous_const (continuous_apply (⟨K, by omega⟩ : Fin (2 * K + 1))).norm)

theorem uniform_product_coefficient_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a ⟨K, by omega⟩‖ → δ ≤ ‖b ⟨K, by omega⟩‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖productCoefficient a b n.val‖ := by
  classical
  let S := (admissibleCoefficients K D δ).prod (admissibleCoefficients K D δ)
  have hc : IsCompact S := (isCompact_admissibleCoefficients K D δ).prod
    (isCompact_admissibleCoefficients K D δ)
  by_cases hs : S.Nonempty
  · obtain ⟨ab, hab, hmin⟩ := hc.exists_isMinOn hs
      (continuous_lowCoefficients K).norm.continuousOn
    have hpos : 0 < ‖lowCoefficients ab‖ := by
      apply norm_pos_iff.mpr
      apply lowCoefficients_ne_zero
      · exact norm_pos_iff.mp (hδ.trans_le hab.1.2)
      · exact norm_pos_iff.mp (hδ.trans_le hab.2.2)
    refine ⟨‖lowCoefficients ab‖, hpos, ?_⟩
    intro a b ha hb ha0 hb0
    have hm : ‖lowCoefficients ab‖ ≤ ‖lowCoefficients (a, b)‖ :=
      hmin ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩
    by_contra hn
    push Not at hn
    have hlt : ‖lowCoefficients (a, b)‖ < ‖lowCoefficients ab‖ :=
      (pi_norm_lt_iff hpos).mpr hn
    exact (not_lt_of_ge hm) hlt
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a b ha hb ha0 hb0
    exact False.elim (hs ⟨(a, b), ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩⟩)

/-- Coefficient of z^r in the two Laurent polynomials supported on [-K,K].
The finite indices enumerate each Laurent exponent exactly once as i-K. -/
noncomputable def laurentProductCoefficient (K : ℕ) (A B : ℤ → ℂ) (r : ℤ) : ℂ :=
  ∑ i : Fin (2 * K + 1), ∑ j : Fin (2 * K + 1),
    if (i.val : ℤ) - K + ((j.val : ℤ) - K) = r then
      A ((i.val : ℤ) - K) * B ((j.val : ℤ) - K) else 0

theorem shifted_productCoefficient (K : ℕ) (A B : ℤ → ℂ) (n : ℕ) :
    productCoefficient (K := K) (fun i => A ((i.val : ℤ) - K))
      (fun i => B ((i.val : ℤ) - K)) n =
    laurentProductCoefficient K A B ((n : ℤ) - 2 * K) := by
  classical
  unfold productCoefficient laurentProductCoefficient
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : (i.val + j.val = n) ↔
      (i.val : ℤ) - K + ((j.val : ℤ) - K) = (n : ℤ) - 2 * K := by omega
  simp only [h]

theorem laurent_product_uniform_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖A v‖ ≤ D) →
      (∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖B v‖ ≤ D) →
      δ ≤ ‖A 0‖ → δ ≤ ‖B 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖laurentProductCoefficient K A B (-(n : ℤ))‖ := by
  obtain ⟨ε, hε, hbound⟩ := uniform_product_coefficient_bound K D δ hδ
  refine ⟨ε, hε, ?_⟩
  intro A B hA hB hA0 hB0
  let a : Coefficients K := fun i => A ((i.val : ℤ) - K)
  let b : Coefficients K := fun i => B ((i.val : ℤ) - K)
  have ha : ∀ i, ‖a i‖ ≤ D := by
    intro i
    apply hA <;> have := i.isLt <;> omega
  have hb : ∀ i, ‖b i‖ ≤ D := by
    intro i
    apply hB <;> have := i.isLt <;> omega
  have ha0 : δ ≤ ‖a ⟨K, by omega⟩‖ := by simpa [a] using hA0
  have hb0 : δ ≤ ‖b ⟨K, by omega⟩‖ := by simpa [b] using hB0
  obtain ⟨i, hi⟩ := hbound a b ha hb ha0 hb0
  have hiK : i.val ≤ 2 * K := by have := i.isLt; omega
  refine ⟨2 * K - i.val, by omega, ?_⟩
  have he : (-((2 * K - i.val : ℕ) : ℤ)) = (i.val : ℤ) - 2 * K := by omega
  rw [he]
  simpa only [a, b, shifted_productCoefficient] using hi

end FiniteFactor

end OAI
