import OAI.NumberTheory.CubicMoment.Estimates.CoprimeOuterComplete

namespace OAI

/-! Uniformize the three primal powers without attaching an epsilon
loss to the zero-frequency A term. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_cost_mono {ε C K Z A N M P : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hK : 0 ≤ K) (hZ : 0 < Z)
    (hZA : Z ≤ A) (hN : 0 ≤ N) (hNM : N ≤ M) (hP : N^3/Z ≤ P) :
    K*Z+C*(N^3/Z)^ε*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) ≤
      K*A+C*P^ε*(M+A^(1/3:ℝ)*M+A^(2/3:ℝ)*M^(2/3:ℝ)) := by
  have hA0 : 0 ≤ A := hZ.le.trans hZA
  have hM0 : 0 ≤ M := hN.trans hNM
  have hP0 : 0 ≤ P := (div_nonneg (pow_nonneg hN 3) hZ.le).trans hP
  apply add_le_add (mul_le_mul_of_nonneg_left hZA hK)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hP hε) hC
  · apply add_le_add
    · exact add_le_add hNM (mul_le_mul
        (Real.rpow_le_rpow hZ.le hZA (by norm_num)) hNM hN (by positivity))
    · exact mul_le_mul (Real.rpow_le_rpow hZ.le hZA (by norm_num))
        (Real.rpow_le_rpow hN hNM (by norm_num)) (by positivity) (by positivity)
  · positivity
  · positivity

lemma quotient_scale_bound {A L Q D B m k : ℝ}
    (hA : 0 < A) (hL : 1 ≤ L) (hQ : 1 ≤ Q) (hD : 1 ≤ D)
    (hk : 1 ≤ k) (hkm : m ≤ k) (hm : 1 ≤ m) (hkL : k ≤ B*L)
    (hB : 1 ≤ B) (hkD : D ≤ k) :
    let Z := A/Q^2/m
    let N := max 1 (L/k)
    0 < Z ∧ 1 ≤ N ∧ Z ≤ A ∧ N ≤ max 1 (L/D) ∧
      N^3/Z ≤ B*Q^2*L^3/A := by
  dsimp only
  have hAp := hA
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hkp : 0 < k := zero_lt_one.trans_le hk
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hmp : 0 < m := zero_lt_one.trans_le hm
  have hZ : 0 < A/Q^2/m := by positivity
  refine ⟨hZ,le_max_left _ _,?_,?_,?_⟩
  · calc
      A/Q^2/m ≤ A/Q^2 := div_le_self (by positivity) hm
      _ ≤ A := div_le_self hA.le (one_le_pow₀ hQ)
  · exact max_le_max_left _ (div_le_div_of_nonneg_left hLp.le hDp hkD)
  · have hp : (max 1 (L/k))^3*m ≤ B*L^3 := by
      by_cases hkL' : k ≤ L
      · rw [max_eq_right ((le_div_iff₀ hkp).mpr (by simpa using hkL'))]
        have hk3 : k ≤ k^3 := le_self_pow₀ hk (by norm_num : (3:ℕ) ≠ 0)
        calc
          (L/k)^3*m ≤ (L/k)^3*k^3 :=
            mul_le_mul_of_nonneg_left (hkm.trans hk3) (by positivity)
          _ = L^3 := by field_simp
          _ ≤ B*L^3 := le_mul_of_one_le_left (by positivity) hB
      · rw [max_eq_left ((div_le_one hkp).mpr (le_of_not_ge hkL'))]
        norm_num only [one_pow,one_mul]
        have hL3 : L ≤ L^3 := le_self_pow₀ hL (by norm_num : (3:ℕ) ≠ 0)
        exact hkm.trans (hkL.trans (mul_le_mul_of_nonneg_left hL3 (zero_le_one.trans hB)))
    rw [show (max 1 (L/k))^3/(A/Q^2/m) =
      ((max 1 (L/k))^3*m)*Q^2/A by field_simp]
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hp (sq_nonneg Q)).trans_eq (by ring)) hA.le

end CubicFirstMoment

end

end OAI
