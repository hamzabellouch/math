import Mathlib

namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (P : Law α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

noncomputable def relativeEntropy (P Q : Law α) : ℝ :=
  ∑ a, P.mass a * Real.log (P.mass a / Q.mass a)

noncomputable def uniformDeficit (P : Law α) : ℝ :=
  Real.log (Fintype.card α) + ∑ a, P.mass a * Real.log (P.mass a)

noncomputable def uniform [Nonempty α] : Law α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

noncomputable def map (P : Law α) (f : α → β) : Law β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then P.mass a else 0
    nonneg := fun b => Finset.sum_nonneg fun a _ => by
      split_ifs <;> simp_all [P.nonneg]
    total := by
      rw [Finset.sum_comm]
      simpa using P.total
  }

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (g ∘ f) := by
  classical
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma pointwise_entropy_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) : p - q ≤ p * Real.log (p / q) := by
  by_cases hq0 : q = 0
  · simp [hq0, hzero hq0]
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  calc
    p - q = q * (p / q - 1) := by field_simp
    _ ≤ q * (p / q * Real.log (p / q)) := h
    _ = p * Real.log (p / q) := by field_simp

lemma relativeEntropy_nonneg (P Q : Law α)
    (hzero : ∀ a, Q.mass a = 0 → P.mass a = 0) :
    0 ≤ P.relativeEntropy Q := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    pointwise_entropy_lower (P.nonneg a) (Q.nonneg a) (hzero a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, P.total, Q.total] using h

lemma relativeEntropy_uniform [Nonempty α] (P : Law α) :
    P.relativeEntropy uniform = P.uniformDeficit := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [relativeEntropy, uniform, one_div, div_inv_eq_mul]
  have hterm (a : α) :
      P.mass a * Real.log (P.mass a * Fintype.card α) =
        P.mass a * Real.log (P.mass a) + P.mass a * Real.log (Fintype.card α) := by
    by_cases ha : P.mass a = 0
    · simp [ha]
    · rw [Real.log_mul ha hc, mul_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.total, one_mul]
  exact add_comm _ _

lemma uniformDeficit_nonneg [Nonempty α] (P : Law α) :
    0 ≤ P.uniformDeficit := by
  rw [← P.relativeEntropy_uniform]
  apply P.relativeEntropy_nonneg
  intro a h
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniform, hc] at h

noncomputable def tilt (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) : Law α where
  mass x := a x / ∑ x, a x
  nonneg x := div_nonneg (ha x) hZ.le
  total := by rw [← Finset.sum_div, div_self hZ.ne']

lemma gibbs_le (P : Law α) (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) (hs : ∀ x, a x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (a x)) -
      (∑ x, P.mass x * Real.log (P.mass x)) ≤ Real.log (∑ x, a x) := by
  have h := P.relativeEntropy_nonneg (tilt a ha hZ) (by
    intro x hx
    exact hs x ((div_eq_zero_iff).mp hx |>.resolve_right hZ.ne'))
  have hterm (x : α) :
      P.mass x * Real.log (P.mass x / (a x / ∑ y, a y)) =
        P.mass x * Real.log (P.mass x) - P.mass x * Real.log (a x) +
          P.mass x * Real.log (∑ y, a y) := by
    by_cases hp : P.mass x = 0
    · simp [hp]
    have hx : a x ≠ 0 := fun hx => hp (hs x hx)
    rw [Real.log_div hp (div_ne_zero hx hZ.ne'), Real.log_div hx hZ.ne']
    ring
  simp only [relativeEntropy, tilt] at h
  simp_rw [hterm] at h
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, P.total,
    one_mul] at h
  unfold mean
  linarith

lemma entropy_moment_bound [Nonempty α] (P : Law α) (f : α → ℝ) :
    P.mean f ≤ P.uniformDeficit +
      Real.log ((∑ x, Real.exp (f x)) / Fintype.card α) := by
  have hZ : 0 < ∑ x, Real.exp (f x) := Finset.sum_pos
    (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  have h := P.gibbs_le (fun x => Real.exp (f x)) (fun x => (Real.exp_pos _).le)
    hZ (fun x hx => False.elim ((Real.exp_ne_zero _) hx))
  simp only [Real.log_exp] at h
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Real.log_div hZ.ne' hc]
  unfold uniformDeficit
  linarith

end Law
end ThorpCompatibility

end OAI
