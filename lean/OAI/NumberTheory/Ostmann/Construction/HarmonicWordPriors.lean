import OAI.NumberTheory.Ostmann.Construction.PrimeCellWordPriors

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeSubsetPrior (P Q : Finset ℕ) (p : P) : ℝ :=
  if (p : ℕ) ∈ Q then (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      (Complex.ofReal (∑ q ∈ Q, (q : ℝ)⁻¹))⁻¹ * ∑ q ∈ Q, ((q : ℝ)⁻¹ : ℂ) * F q := by
  unfold primeSubsetPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (∑ q ∈ Q, (q : ℝ)⁻¹ : ℝ) * F p else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Complex.ofReal_inv]
  ring

theorem primeSubsetPrior_mean_positive (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹) (F : ℕ → ℂ) (δ : ℝ)
    (hb : δ * (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ * (F q).re) :
    δ ≤ (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p).re := by
  rw [primeSubsetPrior_mean P Q hQP F]
  have h := (le_div_iff₀ hm).mpr hb
  simpa only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, zero_mul, mul_zero, sub_zero, Complex.ofReal_mul,
    div_eq_mul_inv, mul_comm] using h

theorem primeSubsetPrior_mean_norm (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) (F : ℕ → ℂ)
    (hF : ∀ p ∈ P, ‖F p‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p‖ ≤ 1 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p : P, primeSubsetPrior P Q p := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (primeSubsetPrior_nonneg P Q p)]
      exact mul_le_of_le_one_right (primeSubsetPrior_nonneg P Q p) (hF p p.property)
    _ = 1 := primeSubsetPrior_mass P Q hQP hm

theorem primeSubsetPrior_cell_mean (P S : Finset ℕ) (hSP : S ⊆ P) (h : ℕ) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P (S.filter (fun q => primeLogIndex q = h)) p : ℂ) * F p) =
      ∑ p : S, (primeCellWordPrior S h p : ℂ) * F p := by
  rw [primeSubsetPrior_mean P _ ((Finset.filter_subset _ _).trans hSP), primeCellWordPrior_mean]
  simp only [complexCellMean, finiteCellMass, Complex.ofReal_inv]

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

theorem primeSubsetPrior_product (P : Finset ℕ) {n : ℕ} (Q : Fin n → Finset ℕ)
    (x : Fin n → P) (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0) :
    productPrior (fun i => primeSubsetPrior P (Q i)) x =
      (∏ i, ∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ * (∏ i, (x i : ℝ))⁻¹ := by
  have hs (i : Fin n) : (x i : ℕ) ∈ Q i :=
    primeSubsetPrior_support P (Q i) (x i) ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
  unfold productPrior
  simp only [primeSubsetPrior, hs, ite_true, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Ostmann

end OAI
