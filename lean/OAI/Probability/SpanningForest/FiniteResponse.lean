import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.FiniteResponse

variable {Ω E : Type*} [Fintype Ω] [Fintype E]

def mean (p : Ω → ℝ) (x : Ω → E → ℝ) (e : E) : ℝ :=
  ∑ ω, p ω * x ω e

def covariance (p : Ω → ℝ) (x : Ω → E → ℝ) (e f : E) : ℝ :=
  (∑ ω, p ω * x ω e * x ω f) - mean p x e * mean p x f

omit [Fintype E] in
lemma mean_nonneg (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hx : ∀ ω e, 0 ≤ x ω e) (e : E) :
    0 ≤ mean p x e := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω) (hx ω e)

omit [Fintype E] in
lemma mean_le_one (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hnorm : ∑ ω, p ω = 1)
    (hx : ∀ ω e, x ω e ≤ 1) (e : E) : mean p x e ≤ 1 := by
  calc
    mean p x e ≤ ∑ ω, p ω := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_of_le_one_right (hp ω) (hx ω e)
    _ = 1 := hnorm

omit [Fintype E] in
lemma covariance_self (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hx : ∀ ω e, x ω e = 0 ∨ x ω e = 1) (e : E) :
    covariance p x e e = mean p x e * (1 - mean p x e) := by
  have hid : (∑ ω, p ω * x ω e * x ω e) = mean p x e := by
    apply Finset.sum_congr rfl
    intro ω _
    rcases hx ω e with h | h <;> simp [h]
  rw [covariance, hid]
  ring

lemma sum_covariance_eq_zero (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hnorm : ∑ ω, p ω = 1) (r : ℝ)
    (hfixed : ∀ ω, ∑ f, x ω f = r) (e : E) :
    ∑ f, covariance p x e f = 0 := by
  have hmean : (∑ f, mean p x f) = r := by
    simp only [mean]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hfixed]
    rw [← Finset.sum_mul, hnorm, one_mul]
  have hsecond : (∑ f, ∑ ω, p ω * x ω e * x ω f) = mean p x e * r := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hfixed]
    rw [← Finset.sum_mul]
    rfl
  simp only [covariance, Finset.sum_sub_distrib]
  rw [hsecond, ← Finset.mul_sum, hmean, sub_self]

lemma sum_abs_of_row_sum_zero (c : E → ℝ) (e : E)
    (hsum : ∑ f, c f = 0) (hdiag : 0 ≤ c e)
    (hoff : ∀ f, f ≠ e → c f ≤ 0) :
    ∑ f, |c f| = 2 * c e := by
  classical
  have hs : (∑ f ∈ Finset.univ.erase e, c f) = -c e := by
    have ht := Finset.sum_erase_add Finset.univ c (Finset.mem_univ e)
    rw [hsum] at ht
    linarith
  rw [← Finset.sum_erase_add Finset.univ (fun f => |c f|) (Finset.mem_univ e)]
  have ha : (∑ f ∈ Finset.univ.erase e, |c f|) =
      -(∑ f ∈ Finset.univ.erase e, c f) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    exact abs_of_nonpos (hoff f (Finset.mem_erase.mp hf).1)
  rw [ha, hs, abs_of_nonneg hdiag]
  ring

theorem covariance_abs_row (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hnorm : ∑ ω, p ω = 1)
    (hx : ∀ ω e, x ω e = 0 ∨ x ω e = 1)
    (r : ℝ) (hfixed : ∀ ω, ∑ f, x ω f = r)
    (hneg : ∀ e f, e ≠ f → covariance p x e f ≤ 0) (e : E) :
    (∑ f, |covariance p x e f|) = 2 * mean p x e * (1 - mean p x e) := by
  have hm0 : 0 ≤ mean p x e := mean_nonneg p x hp (by
    intro ω f
    rcases hx ω f with h | h <;> simp [h]) e
  have hm1 : mean p x e ≤ 1 := mean_le_one p x hp hnorm (by
    intro ω f
    rcases hx ω f with h | h <;> simp [h]) e
  have hd : 0 ≤ covariance p x e e := by
    rw [covariance_self p x hx e]
    exact mul_nonneg hm0 (sub_nonneg.mpr hm1)
  rw [sum_abs_of_row_sum_zero (fun f => covariance p x e f) e
    (sum_covariance_eq_zero p x hnorm r hfixed e) hd
    (fun f hfe => hneg e f (Ne.symm hfe)), covariance_self p x hx e]
  ring

theorem covariance_abs_row_le_half (p : Ω → ℝ) (x : Ω → E → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hnorm : ∑ ω, p ω = 1)
    (hx : ∀ ω e, x ω e = 0 ∨ x ω e = 1)
    (r : ℝ) (hfixed : ∀ ω, ∑ f, x ω f = r)
    (hneg : ∀ e f, e ≠ f → covariance p x e f ≤ 0) (e : E) :
    (∑ f, |covariance p x e f|) ≤ (1 : ℝ) / 2 := by
  rw [covariance_abs_row p x hp hnorm hx r hfixed hneg e]
  nlinarith [sq_nonneg (mean p x e - 1 / 2)]

end Problem336.FiniteResponse

end

end OAI
