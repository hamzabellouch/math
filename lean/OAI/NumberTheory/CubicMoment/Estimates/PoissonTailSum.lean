import OAI.NumberTheory.DirichletL.CubicDyadicDecay
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace OAI

/-! Arbitrarily rapid tails of the actual dyadic Poisson envelope. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_tsum_prefix_tail {F : ℕ → ℂ} (n : ℕ) {A B : ℝ}
    (hf : Summable (fun j => F (j+n)))
    (hprefix : ‖∑ j ∈ Finset.range n, F j‖ ≤ A)
    (htail : ‖∑' j : ℕ, F (j+n)‖ ≤ B) : ‖∑' j : ℕ, F j‖ ≤ A+B := by
  have hs : Summable F := hf.comp_nat_add
  rw [← hs.sum_add_tsum_nat_add n]
  exact (norm_add_le _ _).trans (add_le_add hprefix htail)

lemma poisson_dyadic_tail_majorant {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n j : ℕ) :
    C*(2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^(m+3) ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
  have hpow : (2:ℝ)^n ≤ (2:ℝ)^(j+n) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_left n j)
  have hbase : t*(2:ℝ)^n ≤ 1+t*(2:ℝ)^(j+n) := by nlinarith
  calc
    _ = (C/(1+t*(2:ℝ)^(j+n))^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
      rw [pow_add]
      field_simp
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) hbase m))
      (by positivity)

theorem poisson_dyadic_tail {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n : ℕ) (F : ℕ → ℂ)
    (hF : ∀ j, ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3)) :
    Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤
        (C/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  have hs := (SevenEighths.CubicDyadicDecay.decay_summable t 1 ht (by norm_num)).comp_injective
    (add_left_injective n)
  simp only [Real.rpow_one] at hs
  have hm := hs.mul_left (C/(t*(2:ℝ)^n)^m)
  have hb (j : ℕ) : ‖F (j+n)‖ ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
    (hF (j+n)).trans (poisson_dyadic_tail_majorant ht hC m n j)
  have hsum : Summable (fun j => F (j+n)) := hm.of_norm_bounded hb
  refine ⟨hsum,?_⟩
  have ht' := SevenEighths.CubicDyadicDecay.decay_tail_le t 1 ht (by norm_num) n
  norm_num only [Real.rpow_one,show (1:ℝ)-3 = -2 by norm_num] at ht'
  calc
    _ ≤ ∑' j : ℕ, ‖F (j+n)‖ := norm_tsum_le_tsum_norm (hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb)
    _ ≤ ∑' j : ℕ, (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
      Summable.tsum_le_tsum hb (hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb) hm
    _ = (C/(t*(2:ℝ)^n)^m)*(∑' j : ℕ, (2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := tsum_mul_left
    _ ≤ _ := by
      have htwo : (2:ℝ)^(-2:ℝ) = 1/4 := by norm_num
      simpa only [htwo,show ((1:ℝ)-1/4)⁻¹ = 4/3 by norm_num] using
        mul_le_mul_of_nonneg_left ht' (show 0 ≤ C/(t*(2:ℝ)^n)^m by positivity)

end CubicFirstMoment

end

end OAI
