import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
local instance : DecidableEq J := Classical.decEq J

def sign (b : Bool) : ℝ := if b then 1 else -1

def value (a : J → ℝ) (σ : J → Bool) : ℝ := ∑ j, a j * sign (σ j)

theorem sign_mgf (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) =
      (2 : ℝ) ^ Fintype.card J * ∏ j, Real.cosh (a j) := by
  simp only [value, Real.exp_sum]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (a j * sign b))]
  have h (j : J) : (∑ b : Bool, Real.exp (a j * sign b)) = 2 * Real.cosh (a j) := by
    simp [sign, Real.cosh_eq]
    ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem sign_mgf_le (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp ((∑ j, (a j)^2) / 2) := by
  rw [sign_mgf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∏ j, Real.cosh (a j) ≤ ∏ j, Real.exp ((a j)^2/2) :=
      Finset.prod_le_prod₀ (fun j _ => (Real.cosh_pos _).le) (fun j _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by rw [← Real.exp_sum]; simp only [div_eq_mul_inv, Finset.sum_mul]

theorem value_smul (a : J → ℝ) (t : ℝ) (σ : J → Bool) :
    value (fun j => t * a j) σ = t * value a σ := by
  simp only [value, Finset.mul_sum, mul_assoc]

/-- Finite Markov inequality for the equiprobable sign space. -/
theorem upper_tail_mgf (a : J → ℝ) {t u : ℝ} (ht : 0 ≤ t) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) * Real.exp (t*u) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (t^2 * (∑ j, (a j)^2) / 2) := by
  classical
  let S := univ.filter (fun σ : J → Bool => u < value a σ)
  have h1 : (S.card : ℝ) * Real.exp (t*u) ≤ ∑ σ ∈ S, Real.exp (t * value a σ) := by
    calc
      _ = ∑ σ ∈ S, Real.exp (t*u) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun σ hσ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hσ).2.le ht))
  have h2 : (∑ σ ∈ S, Real.exp (t * value a σ)) ≤ ∑ σ : J → Bool, Real.exp (t * value a σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
  have h3 := sign_mgf_le (fun j => t*a j)
  simp only [value_smul, mul_pow, ← Finset.mul_sum] at h3
  exact h1.trans (h2.trans h3)

/-- One-sided sign tail for coefficients of total squared size 1/k. -/
theorem upper_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (-k*u^2/2) := by
  have h := upper_tail_mgf a (mul_nonneg hk.le hu.le) (u := u)
  rw [ha] at h
  have hexp : (k*u)^2*(1/k)/2 = (-k*u^2/2) + (k*u)*u := by field_simp; ring
  rw [hexp, Real.exp_add, ← mul_assoc] at h
  exact (mul_le_mul_iff_left₀ (Real.exp_pos ((k*u)*u))).mp h


theorem value_neg (a : J → ℝ) (σ : J → Bool) : value (fun j => -a j) σ = -value a σ := by
  simp [value, Finset.sum_neg_distrib]

/-- The two-sided sign-tail bound as a fraction of the finite equiprobable sign space. -/
theorem two_sided_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card J ≤ 2 * Real.exp (-k*u^2/2) := by
  classical
  have hn : ∑ j, (-a j)^2 = 1/k := by simpa only [neg_sq] using ha
  have hp := upper_tail a hk hu ha
  have hm := upper_tail (fun j => -a j) hk hu hn
  have hs : (univ.filter fun σ : J → Bool => u < |value a σ|) ⊆
      (univ.filter fun σ : J → Bool => u < value a σ) ∪
      (univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union, value_neg] at *
    rcases lt_abs.mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) ≤
      (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) +
      (((univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card J)).mpr
  nlinarith


end FiniteSigns
end Dixmier

end

end OAI
