import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
open Function Set
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Taylor

def normalizedTimePower (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (t - a)^m / (m.factorial : ℝ)

theorem normalizedTimePower_contDiff (a : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (normalizedTimePower a m) := by
  unfold normalizedTimePower
  fun_prop

theorem normalizedTimePower_hasDerivAt (a t : ℝ) (m : ℕ) :
    HasDerivAt (normalizedTimePower a (m + 1)) (normalizedTimePower a m t) t := by
  have h := (((hasDerivAt_id t).sub_const a).pow (m + 1)).div_const ((m + 1).factorial : ℝ)
  change HasDerivAt (normalizedTimePower a (m + 1))
    ((m + 1 : ℕ) * (t - a)^(m + 1 - 1) * 1 / ((m + 1).factorial : ℝ)) t at h
  simp only [Nat.add_sub_cancel, mul_one] at h
  have he : (m + 1 : ℕ) * (t - a)^m / ((m + 1).factorial : ℝ) = normalizedTimePower a m t := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, normalizedTimePower]
    have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hm, hm1]
  rw [he] at h
  exact h

theorem normalizedTimePower_deriv (a : ℝ) (m : ℕ) :
    deriv (normalizedTimePower a (m + 1)) = normalizedTimePower a m := by
  funext t
  exact (normalizedTimePower_hasDerivAt a t m).deriv

theorem normalizedTimePower_iteratedDeriv_at_center (a : ℝ) (m k : ℕ) :
    iteratedDeriv k (normalizedTimePower a m) a = if k = m then 1 else 0 := by
  change iteratedDeriv k (fun t : ℝ => (t - a)^m / (m.factorial : ℝ)) a = _
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_sub_const (f := fun t : ℝ => t^m)]
  change iteratedDeriv k (fun t : ℝ => t^m) (a - a) / (m.factorial : ℝ) = _
  rw [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℝ) ≠ 0)
  · simpa only [Nat.cast_zero] using (zero_div (m.factorial : ℝ))

theorem coefficient_timePower_jet (a C : ℝ) (m k : ℕ) :
    iteratedDeriv k (fun t => C * normalizedTimePower a m t) a =
      if k = m then C else 0 := by
  rw [iteratedDeriv_const_mul_field, normalizedTimePower_iteratedDeriv_at_center]
  split_ifs <;> simp

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedDeriv_comp_eq_of_jets {Q : E → F} {f g : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hg : ContDiffAt ℝ ∞ g a)
    (hQ : ContDiffAt ℝ ∞ Q (f a))
    (hjets : ∀ j ≤ n, iteratedDeriv j f a = iteratedDeriv j g a) :
    iteratedDeriv n (Q ∘ f) a = iteratedDeriv n (Q ∘ g) a := by
  have hvalue : f a = g a := by simpa only [iteratedDeriv_zero] using hjets 0 (Nat.zero_le n)
  have hQg : ContDiffAt ℝ ∞ Q (g a) := by rw [← hvalue]; exact hQ
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQ hf (WithTop.coe_le_coe.mpr le_top),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQg hg (WithTop.coe_le_coe.mpr le_top)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hvalue]
  congr 1
  funext j
  exact hjets (c.partSize j) (c.partSize_le j)

theorem iteratedDeriv_add_eq_of_zero_jets {f h : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hh : ContDiffAt ℝ ∞ h a)
    (hzero : ∀ j ≤ n, iteratedDeriv j h a = 0) :
    ∀ j ≤ n, iteratedDeriv j (fun t => f t + h t) a = iteratedDeriv j f a := by
  intro j hj
  rw [iteratedDeriv_fun_add (hf.of_le (WithTop.coe_le_coe.mpr le_top))
    (hh.of_le (WithTop.coe_le_coe.mpr le_top)), hzero j hj, add_zero]

end Composition
end SmoothLocal.Taylor

end

end OAI
