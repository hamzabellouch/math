import OAI.NumberTheory.CubicMoment.Estimates.SmallBUnboundedTail

namespace OAI

/-! The absolute infinite Poisson tail for a bounded coefficient. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bounded_coefficient_energy (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {N M : ℝ} (hN : 0 ≤ N) (hS : ∀ a ∈ S, primary a ∧ norm a ≤ N)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) :
    (∑ a ∈ S, ‖β a‖^2) ≤ 18*N*M^2 := by
  calc
    _ ≤ ∑ _a ∈ S, M^2 := Finset.sum_le_sum (fun a ha =>
      pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
    _ = (S.card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primary_support_card_le S hN hS) (sq_nonneg M)

lemma bounded_poisson_tail_scale {N A : ℝ} (hN : 1 ≤ N)
    (hA : N^(3/2:ℝ) ≤ A) (d : ℕ) :
    N^(-2:ℝ)*N ≤ A^(2/3:ℝ)*N^(5/3:ℝ)*(1+Real.log N)^d := by
  have hNp := zero_lt_one.trans_le hN
  have hA1 : 1 ≤ A := (Real.one_le_rpow hN (by norm_num)).trans hA
  have hlog : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have heq : N^(-2:ℝ)*N = N^(-1:ℝ) := by
    calc
      _ = N^(-2:ℝ)*N^(1:ℝ) := by rw [Real.rpow_one]
      _ = N^((-2:ℝ)+1) := (Real.rpow_add hNp _ _).symm
      _ = _ := by norm_num
  rw [heq]
  calc
    _ ≤ N^(5/3:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ ≤ A^(2/3:ℝ)*N^(5/3:ℝ) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) (Real.one_le_rpow hA1 (by norm_num))
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog)

theorem bounded_poisson_energy_tail (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M A u : ℝ) (n d : ℕ),
      2 ≤ N → N^(3/2:ℝ) ≤ A → N^(3/4:ℝ)/32 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N/2 ≤ norm a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        K*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d := by
  obtain ⟨K,hK,htail⟩ := smallB_poisson_tail_power_unbounded V hV hV'
  refine ⟨18*K,by positivity,?_⟩
  intro S H β N M A u n d hN hAlo hcut hS hβ hH
  have hN1 : 1 ≤ N := by linarith
  have he := bounded_coefficient_energy S β (by linarith : 0 ≤ N)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩) hβ
  obtain ⟨ht,htb⟩ := htail S H β A (N/2) N u n (by linarith) (by linarith) hAlo hcut hS hH
  refine ⟨ht,htb.trans ?_⟩
  calc
    _ ≤ K*N^(-2:ℝ)*(18*N*M^2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = (18*K*M^2)*(N^(-2:ℝ)*N) := by ring
    _ ≤ (18*K*M^2)*(A^(2/3:ℝ)*N^(5/3:ℝ)*(1+Real.log N)^d) :=
      mul_le_mul_of_nonneg_left (bounded_poisson_tail_scale hN1 hAlo d) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
