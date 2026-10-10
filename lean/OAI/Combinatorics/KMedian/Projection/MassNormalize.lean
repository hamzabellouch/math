import Mathlib

namespace OAI

section Inline_PCPMassNormalize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MassNormalize
variable {A : Type} [Fintype A] [Inhabited A]
noncomputable def normalized (f : A → ℝ) (H : ℝ) (a : A) : ℝ :=
  if (∑ a, f a)=0 then (if a=default then H else 0) else (H/(∑ a, f a))*f a

lemma nonneg (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (H : ℝ) (hH : 0 ≤ H) (a : A) :
    0 ≤ normalized f H a := by
  unfold normalized
  split_ifs
  · exact hH
  · exact le_rfl
  · exact mul_nonneg (div_nonneg hH (sum_nonneg (fun a _ => hf a))) (hf a)

lemma total (f : A → ℝ) (H : ℝ) : ∑ a, normalized f H a=H := by
  unfold normalized
  by_cases hz : (∑ a, f a)=0
  · simp only [hz,ite_true]
    simp
  · simp only [hz,ite_false,← mul_sum]
    exact div_mul_cancel₀ H hz

omit [Inhabited A] in
lemma zero_entries (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hz : (∑ a, f a)=0) (a : A) : f a=0 := by
  exact (sum_eq_zero_iff_of_nonneg (fun a _ => hf a)).mp hz a (mem_univ _)

lemma l1_error (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (H : ℝ) (hH : 0 ≤ H) :
    (∑ a, |f a-normalized f H a|)=|(∑ a, f a)-H| := by
  by_cases hz : (∑ a, f a)=0
  · have he : f=fun _ => 0 := funext (zero_entries f hf hz)
    rw [he]
    unfold normalized
    simp only [sum_const_zero,ite_true,zero_sub,abs_neg]
    simp only [apply_ite abs,abs_of_nonneg hH,abs_zero]
    simp
  · have hp : 0 ≤ ∑ a, f a := sum_nonneg (fun a _ => hf a)
    unfold normalized
    simp only [hz,ite_false]
    calc
      _ = ∑ a, |1-H/(∑ a, f a)| *f a := by
        apply sum_congr rfl
        intro a _
        rw [show f a-(H/(∑ a, f a))*f a=(1-H/(∑ a, f a))*f a by ring,
          abs_mul,abs_of_nonneg (hf a)]
      _ = |1-H/(∑ a, f a)| *(∑ a, f a) := (mul_sum _ _ _).symm
      _ = |(1-H/(∑ a, f a))*(∑ a, f a)| := by rw [abs_mul,abs_of_nonneg hp]
      _ = _ := by congr 1; field_simp
end MassNormalize
end MetricKMedian.PCP

end Inline_PCPMassNormalize

end OAI
