import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra
import OAI.Geometry.SurfaceImmersion.Geometry.InitializationPowers

namespace OAI

/-! Initialization at a power of the primitive scale, after all geometric
polynomial losses and before the primitive accuracy order are chosen. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem polynomial_prepared_initialization (E : ℝ → ℝ) (hE : HasPolynomialBound E) :
    ∃ ν : ℝ, 1 < ν ∧ ∃ N : ℕ, ∀ B D e r K : ℝ,
      0 ≤ B → 0 ≤ D → 0 < e → 1 ≤ r → 0 < K →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
        z^ν ≤ z ∧ z^ν ≤ 1/32 ∧
        (∀ ε : ℝ, 0 < ε → ε⁻¹ ≤ E ((z^2)⁻¹) → z^ν < ε) ∧
        B/z^2+(z^ν/z)*(B/z^2) ≤ 1/z^4 ∧
        D+z^ν*D+e ≤ 1/z^4 ∧
        ((z^ν)^(10 : ℝ))^2*(B/z^2) ≤ (z^8/r)/8 ∧
        B*z^(N+1) ≤ ((z^ν)^(10 : ℝ))^2*e ∧
        ((z^ν)^(10 : ℝ))^2*(B/z^2)+2*(z^8/r)*z^ν ≤ z^8/K := by
  obtain ⟨d,hd⟩ := hE.at_inverse_scale 2
  obtain ⟨C,hC,hbound⟩ := hd 1 le_rfl
  let ν : ℝ := (d : ℝ)+2
  have hν : 1 < ν := by dsimp [ν]; linarith [show (0:ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
  obtain ⟨N,hN⟩ := exists_nat_gt (20*ν)
  have hN' : 20*ν < (N : ℝ)+1 := by linarith
  refine ⟨ν,hν,N,?_⟩
  intro B D e r K hB hD he hr hK
  have hrp : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨ηb,hηb,hηb32,hbudget⟩ := initialization_budget_threshold hν hN' hB hD he
  obtain ⟨ηe,hηe,_,heps⟩ := positive_power_threshold C (ν-d) 1 (by dsimp [ν]; linarith) zero_lt_one
  let a := min (1/(8*r)) (1/(2*K))
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  obtain ⟨ηp,hηp,_,hnear⟩ := positive_power_threshold B (20*ν-10) a (by linarith) ha
  obtain ⟨ηt,hηt,_,htail⟩ := positive_power_threshold (2/r) ν (1/(2*K)) (by linarith) (by positivity)
  let η := min ηb (min ηe (min ηp ηt))
  refine ⟨η,lt_min hηb (lt_min hηe (lt_min hηp hηt)),
    (min_le_left _ _).trans (hηb32.trans (by norm_num)),?_⟩
  intro z hz hzη
  have hzb : z < ηb := hzη.trans_le (min_le_left _ _)
  have hze : z < ηe := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzp : z < ηp := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzt : z < ηt := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hz1 : z ≤ 1 := hzη.le.trans ((min_le_left _ _).trans (hηb32.trans (by norm_num)))
  obtain ⟨htz,ht32,hMB,hHB,_,herr⟩ := hbudget z hz hzb
  have hδ : ((z^ν)^(10 : ℝ))^2 = z^(20*ν) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg hz.le _),← Real.rpow_mul hz.le]
    congr 1
    norm_num
    ring
  have hdisp : z^(20*ν)*(B/z^2) = (B*z^(20*ν-10))*z^8 := by
    rw [Real.rpow_sub hz,Real.rpow_ofNat]
    have hp : z^10 = z^2*z^8 := by ring
    rw [hp]
    field_simp
  have hsmall := mul_le_mul_of_nonneg_right (hnear z hz hzp).le (pow_nonneg hz.le 8)
  have hsmallr : z^(20*ν)*(B/z^2) ≤ (z^8/r)/8 := by
    rw [hdisp]
    calc
      _ ≤ a*z^8 := hsmall
      _ ≤ (1/(8*r))*z^8 := mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hz.le _)
      _ = (z^8/r)/8 := by ring
  have hsmallK : z^(20*ν)*(B/z^2) ≤ z^8/(2*K) := by
    rw [hdisp]
    exact hsmall.trans (by
      calc
        a*z^8 ≤ (1/(2*K))*z^8 := mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hz.le _)
        _ = z^8/(2*K) := by ring)
  have htailK : 2*(z^8/r)*z^ν ≤ z^8/(2*K) := by
    have hh := mul_le_mul_of_nonneg_right (htail z hz hzt).le (pow_nonneg hz.le 8)
    convert hh using 1 <;> ring
  refine ⟨htz,ht32,?_,hMB,hHB,?_,?_,?_⟩
  · intro ε hε hεb
    have hEbound : E ((z^2)⁻¹) ≤ C/z^d := by
      simpa only [one_div] using (hbound z hz hz1).2
    have heq : z^ν*(C/z^d) = C*z^(ν-d) := by
      rw [Real.rpow_sub hz,Real.rpow_natCast]
      ring
    have hh : z^ν*ε⁻¹ < 1 := (mul_le_mul_of_nonneg_left (hεb.trans hEbound)
      (Real.rpow_nonneg hz.le _)).trans_lt (by rw [heq]; exact heps z hz hze)
    exact (div_lt_one hε).mp (by simpa only [div_eq_mul_inv] using hh)
  · rwa [hδ]
  · rw [hδ]
    have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
    simpa only [hexp,Real.rpow_natCast] using herr
  · rw [hδ]
    calc
      _ ≤ z^8/(2*K)+z^8/(2*K) := add_le_add hsmallK htailK
      _ = z^8/K := by ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
