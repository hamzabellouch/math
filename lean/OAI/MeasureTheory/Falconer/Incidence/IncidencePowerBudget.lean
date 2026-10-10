import OAI.MeasureTheory.Falconer.Incidence.IncidenceBucketBudget
import OAI.MeasureTheory.Falconer.Estimates.DyadicPolynomialBudget

namespace OAI

/-! Power bounds relating the original radius to the chosen block scale. -/
namespace Falconer

theorem incidence_inverse_scale_power {δ C a : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (N : ℕ) (hscale : 1/(2:ℝ)^N ≤ C*δ) :
    δ^(-a) ≤ C^a*(2:ℝ)^(a*(N:ℝ)) := by
  have hi : δ⁻¹ ≤ C*(2:ℝ)^N := by
    rw [← one_div]
    apply (div_le_iff₀ hδ).2
    have hh := (div_le_iff₀ (show (0:ℝ) < (2:ℝ)^N by positivity)).mp hscale
    nlinarith only [hh]
  rw [Real.rpow_neg_eq_inv_rpow]
  calc
    _ ≤ (C*(2:ℝ)^N)^a := Real.rpow_le_rpow (by positivity) hi ha
    _ = _ := by
      rw [Real.mul_rpow hC (by positivity),← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 2
      ring

theorem incidence_bucket_linear_bound {δ : ℝ} (hδ : 0 < δ) (N B : ℕ)
    (hscale : 1/(2:ℝ)^N ≤ (4*(2:ℝ)^B)*δ) :
    ((Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ):ℝ) ≤ (2*(B:ℝ)+13)*((N:ℝ)+1) := by
  have hh : 1 ≤ 4*(2:ℝ)^(N+B)*δ := by
    have ht := (div_le_iff₀ (show (0:ℝ) < (2:ℝ)^N by positivity)).mp hscale
    rw [pow_add]
    nlinarith only [ht]
  have hc : ((Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ):ℝ) ≤ (2*N+2*B+11:ℕ) :=
    Nat.cast_le.mpr (incidence_bucket_count_bound hδ N B hh)
  push_cast at hc
  have hBN : 0 ≤ (B:ℝ)*(N:ℝ) := mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg N)
  push_cast
  nlinarith only [hc,hBN,Nat.cast_nonneg (α := ℝ) N]

theorem exists_incidence_absorption_parameters {lam ζ : ℝ}
    (hlam : 0 < lam) (hζ : 0 < ζ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/8 ∧ ε ≤ lam/16 ∧ ε ≤ ζ/8 ∧
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
        C*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) ≤ (2:ℝ)^((lam/4)*(N:ℝ)) ∧
        C*(2:ℝ)^((2*ε)*(N:ℝ)) ≤ (2:ℝ)^(ζ*(N:ℝ)) := by
  let ε := min (1/8:ℝ) (min (lam/16) (ζ/8))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1/8 := min_le_left _ _
  have he_lam : ε ≤ lam/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hεζ : ε ≤ ζ/8 := (min_le_right _ _).trans (min_le_right _ _)
  let σ := min (lam/8) (ζ/2)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_polynomial_loss hσ hC 1
  refine ⟨ε,hε,hε1,he_lam,hεζ,N0,hN0,?_⟩
  intro N hN
  have hc : C*((N:ℝ)+1) ≤ (2:ℝ)^(σ*(N:ℝ)) := by
    have hh := hpoly N hN
    rw [pow_one] at hh
    simpa only [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),mul_comm (Real.log 2)] using hh
  have hsigma_lam : σ ≤ lam/8 := min_le_left _ _
  have hσζ : σ ≤ ζ/2 := min_le_right _ _
  constructor
  · calc
      _ ≤ (2:ℝ)^(σ*(N:ℝ))*(2:ℝ)^(ε*(N:ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (2:ℝ)^((σ+ε)*(N:ℝ)) := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hsigma_lam,he_lam,hlam]) (Nat.cast_nonneg N))
  · have hCsmall : C ≤ (2:ℝ)^(σ*(N:ℝ)) :=
      (le_mul_of_one_le_right hC (by linarith only [Nat.cast_nonneg (α := ℝ) N])).trans hc
    calc
      _ ≤ (2:ℝ)^(σ*(N:ℝ))*(2:ℝ)^((2*ε)*(N:ℝ)) := mul_le_mul_of_nonneg_right hCsmall (by positivity)
      _ = (2:ℝ)^((σ+2*ε)*(N:ℝ)) := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hσζ,hεζ,hζ]) (Nat.cast_nonneg N))

end Falconer

end OAI
