import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
open FourierTransform Filter Asymptotics
namespace Ostmann.Construction

theorem schwartz_int_summable (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ)<2))
  exact (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite

theorem poisson_zero_frequency (f : SchwartzMap ℝ ℂ)
    (hband : ∀ n : ℤ, n ≠ 0 → 𝓕 f (n : ℝ) = 0) (x : ℝ) :
    (∑' n : ℤ, f (x + n)) = 𝓕 f 0 := by
  rw [f.tsum_eq_tsum_fourier x]
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    rw [hband n hn, zero_mul]

theorem poisson_of_fourier_support_lt_one (f : SchwartzMap ℝ ℂ)
    (hband : ∀ ξ : ℝ, 1 ≤ |ξ| → 𝓕 f ξ = 0) (x : ℝ) :
    (∑' n : ℤ, f (x + n)) = 𝓕 f 0 := by
  apply poisson_zero_frequency f _ x
  intro n hn
  apply hband
  have hnat : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
  have hInt : (1 : ℤ) ≤ |n| := by
    simpa only [Int.natCast_natAbs] using (show (1 : ℤ) ≤ (n.natAbs : ℤ) by exact_mod_cast hnat)
  exact_mod_cast hInt

end Ostmann.Construction

end

end OAI
