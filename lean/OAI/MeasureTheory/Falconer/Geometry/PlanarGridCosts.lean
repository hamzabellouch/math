import OAI.MeasureTheory.Falconer.Geometry.PlanarGridScales

namespace OAI

/-! Explicit fixed polynomial costs for the original-to-rounded graph
construction. These are absorbed only after the geometric application. -/
namespace Falconer

 theorem planar_grid_polynomial_costs {M L K t A : ℝ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hAM : A ≤ M)
    (_ht : 0 ≤ t) (ht2 : t ≤ 2) :
    let F := 5*(2*(64*M)+3)
    let B := (2*(2*M^2)+3)*(2*M+3)*(2*(64*M^2)+3)
    F ≤ 655*M ∧ L*F^2 ≤ 429025*L*M^2 ∧
      B*L*F ≤ 3003175*L*M^6 ∧
      (K*A^t*4^t)*(128*M^2)^t ≤ 262144*K*M^6 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM2 : 1 ≤ M^2 := by nlinarith
  let F := 5*(2*(64*M)+3)
  let B := (2*(2*M^2)+3)*(2*M+3)*(2*(64*M^2)+3)
  have hF : F ≤ 655*M := by dsimp [F]; linarith
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hB : B ≤ 4585*M^5 := by
    have h0 : 2*(2*M^2)+3 ≤ 7*M^2 := by nlinarith
    have h1 : 2*M+3 ≤ 5*M := by linarith
    have h2 : 2*(64*M^2)+3 ≤ 131*M^2 := by nlinarith
    calc
      B ≤ (7*M^2)*(5*M)*(131*M^2) :=
        mul_le_mul (mul_le_mul h0 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
      _ = 4585*M^5 := by ring
  have hQ : L*F^2 ≤ 429025*L*M^2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hF0 hF 2) hL
    convert hh using 1; ring
  have hBP : B*L*F ≤ 3003175*L*M^6 := by
    calc
      _ ≤ (4585*M^5)*L*(655*M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB hL) hF hF0 (by positivity)
      _ = _ := by ring
  have hAp : A^t ≤ M^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA ht2
    rw [Real.rpow_two] at hh
    exact hh.trans (pow_le_pow_left₀ (zero_le_one.trans hA) hAM 2)
  have h4 : (4:ℝ)^t ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) ht2
    simpa only [Real.rpow_two,show (4:ℝ)^2 = 16 by norm_num] using hh
  have hC : (128*M^2)^t ≤ (128*M^2)^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by nlinarith : 1 ≤ 128*M^2) ht2
    simpa only [Real.rpow_two] using hh
  have hR : (K*A^t*4^t)*(128*M^2)^t ≤ 262144*K*M^6 := by
    calc
      _ ≤ (K*M^2*16)*(128*M^2)^2 :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hAp hK) h4
          (Real.rpow_nonneg (by norm_num) t) (by positivity)) hC
          (Real.rpow_nonneg (by positivity) t) (by positivity)
      _ = _ := by ring
  exact ⟨hF,hQ,hBP,hR⟩

 theorem planar_direction_polynomial_cost {M A K u : ℝ}
    (hM : 1 ≤ M) (hA : 0 ≤ A) (hK : 0 ≤ K) (hu : u ≤ 2) :
    (A*K)*(64*M^2)^u ≤ 4096*A*K*M^4 := by
  have hC : 1 ≤ 64*M^2 := by nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hC hu
  rw [Real.rpow_two] at hp
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hK)
  convert hm using 1; ring

end Falconer

end OAI
