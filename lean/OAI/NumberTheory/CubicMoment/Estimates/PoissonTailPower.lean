import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! The elementary power gap for a cutoff beyond the natural Poisson
scale. The number of integrations by parts is fixed from the gap. -/
noncomputable section
namespace CubicFirstMoment

lemma poisson_cutoff_exists {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlarge : 2 ≤ L^(η/2)) :
    ∃ n : ℕ, L^(1+η/2) ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ L^(1+η) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hx : 1 ≤ L^(1+η/2) := Real.one_le_rpow hL (by linarith)
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 2)
  refine ⟨n+1,hn'.le,?_⟩
  have hup : (2:ℝ)^(n+1) ≤ L^(1+η) := by
    calc
      _ ≤ 2*L^(1+η/2) := by rw [pow_succ]; nlinarith
      _ ≤ L^(η/2)*L^(1+η/2) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  intro j hj
  calc
    _ = (2:ℝ)^(j+1) := by rw [pow_succ]; ring
    _ ≤ (2:ℝ)^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ _ := hup

lemma poisson_cutoff_scale {L A J K η : ℝ} (hL : 1 ≤ L) (hη : η ≤ 1)
    (hA : L^(1-η/4) ≤ A) (hJ : L^(1+η/2) ≤ J) (hK : 0 < K) :
    1/(K*L^2) ≤ A/(K*L^2) ∧
      L^(η/4)/K ≤ (A/(K*L^2))*J := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA₁ : 1 ≤ A := (Real.one_le_rpow hL (by linarith)).trans hA
  constructor
  · exact div_le_div_of_nonneg_right hA₁ (by positivity)
  · have hpow : L^(1-η/4)*L^(1+η/2) = L^(η/4)*L^2 := by
      rw [← Real.rpow_add hLp,← Real.rpow_natCast L 2,← Real.rpow_add hLp]
      congr 1
      push_cast
      ring
    calc
      _ = (L^(1-η/4)*L^(1+η/2))/(K*L^2) := by rw [hpow]; field_simp
      _ ≤ (A*J)/(K*L^2) := div_le_div_of_nonneg_right
        (mul_le_mul hA hJ (by positivity) (by linarith)) (by positivity)
      _ = _ := by ring

lemma poisson_tail_power_gap {L A t J K α : ℝ} (hL : 1 ≤ L) (_hA : 0 ≤ A)
    (hAL : A ≤ L^2) (ht : 0 < t) (hJ : 0 < J) (hK : 0 < K)
    (htL : 1/(K*L^2) ≤ t) (hcut : L^α/K ≤ t*J)
    (m : ℕ) (hm : 11 ≤ α*m) :
    A*L*t^(-3:ℝ)/(t*J)^m ≤ K^(m+3)*L^(-2:ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hit : t⁻¹ ≤ K*L^2 := by
    rw [← one_div,div_le_iff₀ ht]
    have hh := (div_le_iff₀ (show 0 < K*L^2 by positivity)).mp htL
    nlinarith
  have ht3 : t^(-3:ℝ) ≤ K^3*L^6 := by
    rw [Real.rpow_neg ht.le,Real.rpow_ofNat,← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hit 3).trans_eq
    ring
  have hiq : (t*J)⁻¹ ≤ K/(L^α) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hJ),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ hK).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp α)).mpr
    nlinarith
  have hqm : ((t*J)^m)⁻¹ ≤ K^m*L^(-(α*m)) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hiq m).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hLp.le,Real.rpow_neg hLp.le]
    ring
  have hAp : A*L ≤ L^3 := by nlinarith
  calc
    _ ≤ L^3*(K^3*L^6)*(K^m*L^(-(α*m))) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul hAp ht3 (Real.rpow_nonneg ht.le _) (by positivity))
        hqm (by positivity) (by positivity)
    _ = K^(m+3)*L^(9-α*m) := by
      rw [pow_add,Real.rpow_sub hLp]
      rw [Real.rpow_ofNat,Real.rpow_neg hLp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

end CubicFirstMoment

end

end OAI
