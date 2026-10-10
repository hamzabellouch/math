import OAI.MeasureTheory.Falconer.Radial.WeakRadialTotalCost
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

/-! # Quantitative estimates on the retained interval of dyadic scales -/

namespace Falconer
open scoped BigOperators ENNReal

lemma radial_scale_window_half {K N : ℕ} (hK : 0 < K) (hN : 2*K ≤ N) :
    N ≤ 2*K*(N/K) := by
  have hq : 2 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
  have hr := Nat.mod_lt N hK
  have he := Nat.div_add_mod N K
  nlinarith

lemma radial_scale_window_loss {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^N)^(a/(2*(K:ℝ))) ≤ ((2:ℝ)^j)^a := by
  have he : (N:ℝ) ≤ 2*(K:ℝ)*(j:ℝ) := by
    exact_mod_cast (radial_scale_window_half hK hN).trans (Nat.mul_le_mul_left (2*K) hj)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < 2*K)).mp
  have hh := mul_le_mul_of_nonneg_right he ha
  calc
    (2*K)*((N:ℝ)*(a/(2*(K:ℝ)))) = (N:ℝ)*a := by field_simp
    _ ≤ (2*(K:ℝ)*(j:ℝ))*a := hh
    _ = (2*K)*((j:ℝ)*a) := by ring

lemma radial_scale_window_decay {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^j)^(-a) ≤ ((2:ℝ)^N)^(-(a/(2*(K:ℝ)))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) (radial_scale_window_loss hK hN hj ha)

theorem radial_scale_window_cost (K : ℕ) (hK : 0 < K) {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ j ∈ Finset.Icc (N/K) N, ENNReal.ofReal (((2:ℝ)^j)^(-a))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let c : ℝ := a/(4*(K:ℝ))
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Np,hp⟩ := PlanarFalconer.fixed_polynomial_subpower 1 hc
  refine ⟨c,hc,2*K+Np,?_⟩
  intro N hN
  have hhalf : 2*K ≤ N := by omega
  have hpoly : (N:ℝ)+1 ≤ ((2:ℝ)^N)^c := by
    apply le_trans _ (hp N (by omega))
    simp only [pow_one]
    linarith [show (0:ℝ) ≤ N by positivity]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (N/K) N,
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal (radial_scale_window_decay hK hhalf
        (Finset.mem_Icc.mp hj).1 ha.le)
    _ = ((Finset.Icc (N/K) N).card:ℝ≥0∞)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by simp
    _ ≤ ((N:ℝ≥0∞)+1)*ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      gcongr
      exact_mod_cast (show (Finset.Icc (N/K) N).card ≤ N+1 by simp)
    _ = ENNReal.ofReal (((N:ℝ)+1)*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    _ ≤ ENNReal.ofReal (((2:ℝ)^N)^c*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpoly (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 2
      dsimp [c]
      ring

end Falconer

end OAI
