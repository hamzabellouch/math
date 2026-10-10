import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem schwartz_summable_int (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => f (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem schwartz_summable_fourier_phase (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ => 𝓕 f (n : ℝ) * fourier n (x : UnitAddCircle)) := by
  apply Summable.of_norm
  have hn : ∀ n : ℤ, ‖fourier n (x : UnitAddCircle)‖ = 1 := fun _ => Circle.norm_coe _
  simpa only [norm_mul, hn, mul_one] using (schwartz_summable_int (𝓕 f)).norm

theorem finite_weighted_poisson {ι : Type*} (R : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) (f : 𝓢(ℝ, ℂ)) :
    (∑ a ∈ R, c a * ∑' n : ℤ, f (x a + n)) =
      ∑' h : ℤ, (∑ a ∈ R, c a * fourier h (x a : UnitAddCircle)) * 𝓕 f (h : ℝ) := by
  simp_rw [f.tsum_eq_tsum_fourier, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun a _ => (schwartz_summable_fourier_phase f (x a)).mul_left (c a))]
  apply tsum_congr
  intro h
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem residue_weighted_poisson (q : ℕ) (c : ℕ → ℂ) (f : 𝓢(ℝ, ℂ)) :
    (∑ a ∈ Finset.range q, c a * ∑' n : ℤ, f ((a : ℝ) / q + n)) =
      ∑' h : ℤ, (∑ a ∈ Finset.range q,
        c a * fourier h (((a : ℝ) / q : ℝ) : UnitAddCircle)) * 𝓕 f (h : ℝ) :=
  finite_weighted_poisson (Finset.range q) c (fun a => (a : ℝ) / q) f

end Ostmann.QuadraticSieve

end OAI
