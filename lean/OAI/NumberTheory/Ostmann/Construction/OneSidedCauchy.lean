import OAI.NumberTheory.Ostmann.Preliminaries.SubprobabilityTransfer
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedCorrelationEnergy

namespace OAI

/-! # Cauchy--Schwarz for the one-sided character interaction

The long-variable unary restriction is removed before extending its prior.
The diagonal short-variable pairs cost only their maximum atom.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem weighted_family_energy_le_atom {A B : Type*} [Fintype A] [Fintype B]
    (η : A → ℝ) (ν : B → ℝ) (V : B → ℂ) (F : B → A → ℂ)
    (α D ε : ℝ) (hα : 0 ≤ α) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hν : ∀ q, 0 ≤ ν q) (hmass : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hV : ∀ q, ‖V q‖ ≤ 1)
    (hcorr : ∀ q r, ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
      if q = r then D else ε) :
    (∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2) ≤ α * D + ε := by
  have hc (q : B) : ‖(ν q : ℂ) * V q‖ ≤ ν q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν q)]
    exact mul_le_of_le_one_right (hν q) (hV q)
  have hs := weighted_sum_energy_le_correlations Finset.univ Finset.univ η
    (fun q => (ν q : ℂ) * V q) F
  have hpair (q r : B) :
      (‖(ν q : ℂ) * V q‖ * ‖(ν r : ℂ) * V r‖) *
          ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
        D * (if q = r then ν q ^ 2 else 0) + ε * (ν q * ν r) := by
    calc
      _ ≤ (ν q * ν r) * (if q = r then D else ε) :=
        mul_le_mul (mul_le_mul (hc q) (hc r) (norm_nonneg _) (hν q)) (hcorr q r)
          (norm_nonneg _) (mul_nonneg (hν q) (hν r))
      _ ≤ _ := by
        split_ifs with h
        · subst r
          nlinarith [mul_nonneg hε (sq_nonneg (ν q))]
        · ring_nf
          exact le_refl _
  have hsum : (∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2) ≤
      D * (∑ q, ν q ^ 2) + ε * (∑ q, ν q) ^ 2 := by
    apply hs.trans
    calc
      _ ≤ (∑ q, ∑ r, (D * (if q = r then ν q ^ 2 else 0) + ε * (ν q * ν r))) :=
        Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun r _ => hpair q r))
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        have hd : (∑ q, ∑ r : B, D * (if q = r then ν q ^ 2 else 0)) = D * ∑ q, ν q ^ 2 := by
          simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        have he : (∑ q, ∑ r, ε * (ν q * ν r)) = ε * (∑ q, ν q) ^ 2 := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          ring
        rw [hd, he]
  have hsquare : (∑ q, ν q ^ 2) ≤ α := by
    calc
      _ ≤ ∑ q, α * ν q := Finset.sum_le_sum (fun q _ => by
        nlinarith [mul_le_mul_of_nonneg_right (hatom q) (hν q)])
      _ = α * ∑ q, ν q := (Finset.mul_sum _ _ _).symm
      _ ≤ α := mul_le_of_le_one_right hα hmass
  have hmass0 : 0 ≤ ∑ q, ν q := Finset.sum_nonneg (fun q _ => hν q)
  have hmass2 : (∑ q, ν q) ^ 2 ≤ 1 := by nlinarith
  apply hsum.trans
  have hd := mul_le_mul_of_nonneg_left hsquare hD
  have he := mul_le_mul_of_nonneg_left hmass2 hε
  nlinarith

/-- Bounded unary factors on both variables are permitted. The extension
measure need not have mass one; its diagonal cost is recorded in D. -/
theorem one_sided_cauchy_bound {A B : Type*} [Fintype A] [Fintype B]
    (μ η : A → ℝ) (ν : B → ℝ) (U : A → ℂ) (V : B → ℂ) (F : B → A → ℂ)
    (C α D ε : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hμ : ∀ p, 0 ≤ μ p) (hmassμ : ∑ p, μ p ≤ 1)
    (hdom : ∀ p, μ p ≤ C * η p)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1)
    (hcorr : ∀ q r, ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤
      if q = r then D else ε) :
    ‖∑ p, (μ p : ℂ) * (U p * ∑ q, (ν q : ℂ) * V q * F q p)‖ ^ 2 ≤
      C * (α * D + ε) := by
  apply (subprobability_weighted_norm_sq_le μ hμ hmassμ _).trans
  calc
    _ ≤ ∑ p, μ p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hU p)
    _ ≤ C * ∑ p, η p * ‖∑ q, (ν q : ℂ) * V q * F q p‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hdom p) (sq_nonneg ‖∑ q, (ν q : ℂ) * V q * F q p‖)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_family_energy_le_atom η ν V F α D ε hα hD hε hν hmassν hatom hV hcorr) hC

theorem diagonal_correlation_envelope {A : Type*} [Fintype A]
    (η : A → ℝ) (F : A → ℂ) (H B : ℝ)
    (hη : ∀ p, 0 ≤ η p) (hmass : ∑ p, η p ≤ H) (hF : ∀ p, ‖F p‖ ≤ B) :
    ‖∑ p, (η p : ℂ) * (F p * conj (F p))‖ ≤ H * B ^ 2 := by
  calc
    _ ≤ ∑ p, ‖(η p : ℂ) * (F p * conj (F p))‖ := norm_sum_le _ _
    _ = ∑ p, η p * ‖F p‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hη p), pow_two]
    _ ≤ ∑ p, η p * B ^ 2 := Finset.sum_le_sum (fun p _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hF p) 2) (hη p))
    _ ≤ H * B ^ 2 := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hmass (sq_nonneg B)

/-- Only the off-diagonal character correlations require cancellation.
The diagonal estimate follows from the envelope and maximum short atom. -/
theorem one_sided_cauchy_of_offdiagonal {A B : Type*} [Fintype A] [Fintype B]
    (μ η : A → ℝ) (ν : B → ℝ) (U : A → ℂ) (V : B → ℂ) (F : B → A → ℂ)
    (C α H B₀ ε : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hμ : ∀ p, 0 ≤ μ p) (hmassμ : ∑ p, μ p ≤ 1)
    (hdom : ∀ p, μ p ≤ C * η p) (hη : ∀ p, 0 ≤ η p) (hmassη : ∑ p, η p ≤ H)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) (hF : ∀ q p, ‖F q p‖ ≤ B₀)
    (hoff : ∀ q r, q ≠ r →
      ‖∑ p, (η p : ℂ) * (F q p * conj (F r p))‖ ≤ ε) :
    ‖∑ p, (μ p : ℂ) * (U p * ∑ q, (ν q : ℂ) * V q * F q p)‖ ^ 2 ≤
      C * (α * (H * B₀ ^ 2) + ε) := by
  apply one_sided_cauchy_bound μ η ν U V F C α (H * B₀ ^ 2) ε
    hC hα (mul_nonneg hH (sq_nonneg B₀)) hε hμ hmassμ hdom hν hmassν hatom hU hV
  intro q r
  by_cases hqr : q = r
  · subst r
    rw [ite_eq_left rfl]
    exact diagonal_correlation_envelope η (F q) H B₀ hη hmassη (hF q)
  · rw [ite_eq_right hqr]
    exact hoff q r hqr

end Ostmann

end OAI
