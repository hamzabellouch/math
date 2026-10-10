import OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedLogPolynomial
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseFromPolynomial

namespace OAI

/-! An absolute logarithmic phase estimate on every prefix of a dyadic block.
The only size restriction separates off finitely many small blocks. -/
namespace TwoPointCorrelations

open Finset Complex

theorem halasz_log_phase_bound : ∃ C : ℝ, 1≤C ∧ ∀ N H : ℕ,
    1≤N → H≤N → ∀ a t lam : ℝ, a∈Set.Icc (0:ℝ) 1 → 49/100≤lam →
    (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2 → |t|=(N:ℝ)^lam →
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log ((N:ℝ)+a+n):ℝ):ℂ))‖≤
      (N:ℝ)*(C*(lam+1)^6*(N:ℝ)^(-1/((10^15:ℝ)*lam^2)))+
        4*(N:ℝ)^(2/3:ℝ) := by
  obtain ⟨R₁,hR₁⟩ := halasz_bounded_log_polynomial
  obtain ⟨R₂,hR₂⟩ := halasz_large_log_polynomial_saving
  let R := max R₁ R₂
  let C : ℝ := (R+200:ℝ)^6
  have hC : 1≤C := by
    dsimp only [C]
    exact one_le_pow₀ (by have := (Nat.cast_nonneg R : (0:ℝ)≤R); linarith)
  refine ⟨C,hC,?_⟩
  intro N H hN hH a t lam ha hlam hhalf ht
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  have hlam0 : 0<lam := by linarith
  have hlam1 : 1≤lam+1 := by linarith
  have hC0 : 0≤C := by linarith
  have hA0 : 0≤C*(lam+1)^6*(N:ℝ)^(-1/((10^15:ℝ)*lam^2)) := by positivity
  by_cases hsmall : lam≤48
  · obtain ⟨k,hk,hkhi,htay,hpoly⟩ := hR₁ lam hlam hsmall
    apply halasz_phase_from_polynomial hN hH ha (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)≤1/3) hA0 hhalf ht
      (by convert htay using 1; ring)
    intro z hz
    have hM := halasz_short_scale_bounds hNR (by norm_num : (0:ℝ)≤1/3)
    have hp := hpoly (halaszShortScale N (1/3)) hM.1 t z N
      (halasz_short_scale_le_base hNR (by norm_num) (by norm_num)) hz.1 hz.2 ht hM.2.1
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
    calc
      (R₁+182:ℝ)^6 ≤ C := by
        apply pow_le_pow_left₀ (by positivity)
        have hR : R₁≤R := le_max_left _ _
        have hRR : (R₁:ℝ)≤R := by exact_mod_cast hR
        linarith
      _ ≤ C*(lam+1)^6 := le_mul_of_one_le_right hC0 (one_le_pow₀ hlam1)
  · have hlarge : 48≤lam := by linarith
    obtain ⟨hm,hlo,hhi,hkbound⟩ := halasz_large_degree_selection hlarge
    let m := ⌈lam/6⌉₊
    apply halasz_phase_from_polynomial (k := 12*m) hN hH ha
      (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1/3) hA0 hhalf ht
    · have hh := halasz_large_taylor_exponent (m := m) hhi
      convert hh using 1; push_cast; ring
    · intro z hz
      have hM := halasz_short_scale_bounds hNR (by norm_num : (0:ℝ)≤1/4)
      have hp := hR₂ m hm (halaszShortScale N (1/4)) hM.1 t z N lam
        (halasz_short_scale_le_base hNR (by norm_num) (by norm_num)) hz.1 hz.2
        ht hM.2.1 hlo hhi
      apply hp.trans
      apply mul_le_mul
      · calc
          (R₂+12*m+32:ℝ)^6 ≤ ((R+200:ℝ)*(lam+1))^6 := by
            apply pow_le_pow_left₀ (by positivity)
            have hR : R₂≤R := le_max_right _ _
            have hRR : (R₂:ℝ)≤R := by exact_mod_cast hR
            have hR0 : 0≤(R:ℝ) := Nat.cast_nonneg _
            have hRL : 0≤(R:ℝ)*lam := mul_nonneg hR0 hlam0.le
            dsimp only [m]
            nlinarith
          _ = C*(lam+1)^6 := by rw [mul_pow]
      · apply Real.rpow_le_rpow_of_exponent_le hNR
        rw [neg_div,neg_div]
        apply neg_le_neg
        apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<10^8*lam^2)
        nlinarith [sq_nonneg lam]
      · exact Real.rpow_nonneg hN0.le _
      · positivity

end TwoPointCorrelations

end OAI
