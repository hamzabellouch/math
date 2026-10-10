import OAI.NumberTheory.Ostmann.Construction.AllMultipleTupleWeight
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Repeated tuples under the original normalized harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_all_multiple_mass_le {A : Type*} [Fintype A] (n : ℕ)
    (w : A → ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (μ : Fin n → A → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, μ i a ≤ c i * w a)
    (E : Finset (Fin n → A)) (hE : E ⊆ allMultipleTuples A n)
    (ρ : ℝ) (hsmall : ∀ x ∈ E, (∏ i, w (x i)) ≤ ρ) :
    (∑ x ∈ E, productPrior μ x) ≤
      ((∏ i, c i) * Real.sqrt ρ) * ((n : ℝ) ^ n * Real.exp (∑ a, w a)) := by
  have hpoint (x : Fin n → A) (hx : x ∈ E) :
      productPrior μ x ≤ ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) := by
    have hsquare : (∏ i, Real.sqrt (w (x i))) ^ 2 = ∏ i, w (x i) := by
      rw [← Finset.prod_pow]
      simp only [Real.sq_sqrt (hw0 _)]
    have hs : (∏ i, Real.sqrt (w (x i))) ≤ Real.sqrt ρ :=
      Real.le_sqrt_of_sq_le (hsquare.trans_le (hsmall x hx))
    calc
      productPrior μ x ≤ ∏ i, c i * w (x i) :=
        Finset.prod_le_prod₀ (fun i _ => hμ i (x i)) (fun i _ => hbound i (x i))
      _ = (∏ i, c i) * (∏ i, Real.sqrt (w (x i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, hsquare]
      _ ≤ ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) := by
        rw [pow_two, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (Finset.prod_nonneg (fun i _ => hc i)))
          (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
  have hsum : (∑ x ∈ E, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun x _ _ => Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))).trans
      (all_multiple_tuple_weight_exp n w hw0 hw1)
  calc
    _ ≤ ∑ x ∈ E, ((∏ i, c i) * Real.sqrt ρ) * ∏ i, Real.sqrt (w (x i)) :=
      Finset.sum_le_sum hpoint
    _ = ((∏ i, c i) * Real.sqrt ρ) * ∑ x ∈ E, ∏ i, Real.sqrt (w (x i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (Finset.prod_nonneg (fun i _ => hc i)) (Real.sqrt_nonneg _))

theorem harmonic_all_multiple_mass_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (R : ℝ) (hR : 0 < R)
    (hprod : ∀ x ∈ E, R ≤ ∏ i, (x i : ℝ)) :
    (∑ x ∈ E, productPrior (fun i => primeSubsetPrior P (Q i)) x) ≤
      ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (Real.sqrt R)⁻¹) *
        ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by
  have hw1 (p : P) : (p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p p.property).one_lt.le
    exact inv_le_one_of_one_le₀ hp1
  have hsmall (x : Fin n → P) (hx : x ∈ E) : (∏ i, (x i : ℝ)⁻¹) ≤ R⁻¹ := by
    rw [Finset.prod_inv_distrib]
    exact inv_anti₀ hR (hprod x hx)
  simpa only [Real.sqrt_inv] using weighted_all_multiple_mass_le n
    (fun p : P => (p : ℝ)⁻¹) (fun p => by positivity) hw1
    (fun i => (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) (fun i => by positivity)
    (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i p => primeSubsetPrior_atom P (Q i) p) E hE R⁻¹ hsmall

theorem harmonic_all_multiple_integral_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (R : ℝ) (hR : 0 < R)
    (hprod : ∀ x ∈ E, R ≤ ∏ i, (x i : ℝ))
    (F : (Fin n → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x ∈ E, ‖F x‖ ≤ B) :
    ‖∑ x ∈ E, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) * F x‖ ≤
      B * (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (Real.sqrt R)⁻¹) *
        ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹))) := by
  let μ := fun i => primeSubsetPrior P (Q i)
  have hn (x : Fin n → P) : 0 ≤ productPrior μ x :=
    productPrior_nonneg μ (fun i p => primeSubsetPrior_nonneg P (Q i) p) x
  calc
    _ ≤ ∑ x ∈ E, ‖(productPrior μ x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ E, B * productPrior μ x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn x)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hF x hx) (hn x)
    _ = B * ∑ x ∈ E, productPrior μ x := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_all_multiple_mass_le P hP n Q E hE R hR hprod) hB

theorem inverse_sqrt_exp_product (X D : ℝ) (hX : 0 < X) :
    X * (Real.sqrt (X * Real.exp D))⁻¹ =
      Real.sqrt X * Real.exp (-(D / 2)) := by
  rw [Real.sqrt_mul hX.le, ← Real.exp_half, mul_inv, Real.exp_neg]
  have hx : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  field_simp
  nlinarith [hs]

/-- The exact square-root scale of the all-multiple error, before choosing
the large gap constant. The harmonic normalizers are retained explicitly. -/
theorem harmonic_repeated_gap_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (E : Finset (Fin n → P))
    (hE : E ⊆ allMultipleTuples P n) (X D C : ℝ) (hX : 0 < X) (hC : 0 ≤ C)
    (hprod : ∀ x ∈ E, X * Real.exp D ≤ ∏ i, (x i : ℝ))
    (F : (Fin n → P) → ℂ) (hF : ∀ x ∈ E, ‖F x‖ ≤ X * C) :
    ‖∑ x ∈ E, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) * F x‖ ≤
      Real.sqrt X * (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  have hb := harmonic_all_multiple_integral_bound P hP n Q E hE
    (X * Real.exp D) (mul_pos hX (Real.exp_pos _)) hprod F (X * C) (mul_nonneg hX.le hC) hF
  have he : X * C * (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
      (Real.sqrt (X * Real.exp D))⁻¹) * ((n : ℝ) ^ n * Real.exp (∑ p : P, (p : ℝ)⁻¹))) =
      Real.sqrt X * (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
    rw [Real.exp_sub]
    have hxs := inverse_sqrt_exp_product X D hX
    rw [Real.exp_neg] at hxs
    calc
      _ = (X * (Real.sqrt (X * Real.exp D))⁻¹) *
          (C * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
            Real.exp (∑ p : P, (p : ℝ)⁻¹)) := by ring
      _ = _ := by rw [hxs]; ring
  exact he ▸ hb

end Ostmann

end OAI
