import Mathlib
import OAI.Probability.ThorpCompatibility.LightRescaling

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma mean_sum {ι : Type*} [Fintype ι] (P : Law α) (f : ι → α → ℝ) :
    P.mean (fun a => ∑ i, f i a) = ∑ i, P.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

lemma mean_nonneg (P : Law α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ P.mean f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (hf a)

lemma mean_mono_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.mean f ≤ P.mean g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha)))
      (P.nonneg a)

lemma heavy_mass_bound (P R : Law α) {H : ℝ} (hH : 0 < H)
    (hs : ∀ a, R.mass a = 0 → P.mass a = 0) :
    (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) ≤
      P.relativeEntropy R := by
  have hterm (a : α) :
      (if H * R.mass a < P.mass a then P.mass a * (Real.log H - 1) else 0) +
        (P.mass a - R.mass a) ≤ P.mass a * Real.log (P.mass a / R.mass a) := by
    by_cases hh : H * R.mass a < P.mass a
    · rw [ite_eq_left hh]
      have hp : 0 < P.mass a := lt_of_le_of_lt (mul_nonneg hH.le (R.nonneg a)) hh
      have hq : 0 < R.mass a := lt_of_le_of_ne (R.nonneg a) (by
        intro h; exact hp.ne' (hs a h.symm))
      have hl : Real.log H ≤ Real.log (P.mass a / R.mass a) :=
        Real.log_le_log hH ((lt_div_iff₀ hq).mpr hh).le
      have hm := mul_le_mul_of_nonneg_left hl hp.le
      nlinarith [R.nonneg a]
    · rw [ite_eq_right hh, zero_add]
      exact pointwise_entropy_lower (P.nonneg a) (R.nonneg a) (hs a)
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hterm a
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, P.total, R.total,
    sub_self, add_zero] at hsum
  have he : (∑ a, if H * R.mass a < P.mass a then P.mass a * (Real.log H - 1) else 0) =
      (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) := by
    rw [prob, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rwa [he] at hsum

lemma neg_log_mean_le (P : Law α) (f : α → ℝ)
    (hf : ∀ a, 0 < P.mass a → 0 < f a) (hmean : 0 < P.mean f) :
    -Real.log (P.mean f) ≤ P.mean (fun a => -Real.log (f a)) := by
  have ht (a : α) (ha : 0 < P.mass a) :
      Real.log (f a) ≤ Real.log (P.mean f) + f a / P.mean f - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hf a ha) hmean)
    rw [Real.log_div (hf a ha).ne' hmean.ne'] at h
    linarith
  have hm := P.mean_mono_support ht
  have he : P.mean (fun a => Real.log (P.mean f) + f a / P.mean f - 1) =
      Real.log (P.mean f) := by
    rw [P.mean_sub, P.mean_add, P.mean_const, P.mean_const]
    simp only [div_eq_mul_inv]
    rw [P.mean_mul_const, mul_inv_cancel₀ hmean.ne']
    ring
  rw [he] at hm
  have hn : P.mean (fun a => -Real.log (f a)) = -P.mean (fun a => Real.log (f a)) := by
    simp [mean, mul_neg, Finset.sum_neg_distrib]
  rw [hn]
  linarith

lemma uniform_mean_equiv [Nonempty α] (e : α ≃ α) (f : α → ℝ) :
    (uniform : Law α).mean (fun a => f (e a)) = (uniform : Law α).mean f := by
  simp only [mean, uniform, ← Finset.mul_sum, e.sum_comp]

lemma uniform_prob_equiv [Nonempty α] (e : α ≃ α) (S : α → Prop) :
    (uniform : Law α).prob (fun a => S (e a)) = (uniform : Law α).prob S := by
  rw [prob_eq_mean, prob_eq_mean]
  exact uniform_mean_equiv e (fun a => if S a then 1 else 0)

end Law
end ThorpCompatibility

end OAI
