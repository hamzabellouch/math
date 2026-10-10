import OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedSaving

namespace OAI

/-! Uniform bounded-degree polynomial estimate and Taylor margin. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_bounded_log_polynomial : ∃ R₀ : ℕ, ∀ lam : ℝ,
    49/100≤lam → lam≤48 → ∃ k : ℕ, 2≤k ∧ k≤150 ∧
      lam-((k:ℝ)+1)/3≤-(1/2:ℝ) ∧
      ∀ M : ℕ, 1≤M → ∀ t z N : ℝ, (M:ℝ)≤N → N≤z → z≤2*N →
      |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
        (R₀+182:ℝ)^6*N^(-1/((10^15:ℝ)*lam^2)) := by
  obtain ⟨R₀,hR⟩ := halasz_single_log_polynomial_saving
  refine ⟨R₀,?_⟩
  intro lam hlo hhi
  have hfinish (k d : ℕ) (hk : 2≤k) (hkhi : k≤150) (hd : 1≤d) (hdk : d≤k)
      (hdeg : (1:ℝ)/32+(k:ℝ)^2/1024≤
        min ((d:ℝ)/3) (min ((d:ℝ)-lam) (lam-(d:ℝ)/3))) :
      ∀ M : ℕ,1≤M → ∀ t z N : ℝ,(M:ℝ)≤N → N≤z → z≤2*N →
      |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
        (R₀+182:ℝ)^6*N^(-1/((10^15:ℝ)*lam^2)) := by
    intro M hM t z N hMN hz hzhi ht hscale
    have hp := hR k hk M hM d hd hdk t z N lam (1/32) hMN hz hzhi ht hscale hdeg
    have hN : 1≤N := (show (1:ℝ)≤M by exact_mod_cast hM).trans hMN
    have he := neg_le_neg (halasz_bounded_root_saving hk hkhi hlo)
    have he' : -(1/32:ℝ)/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)≤
        -1/((10^15:ℝ)*lam^2) := by simpa only [neg_div] using he
    apply hp.trans
    apply mul_le_mul
    · apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show R₀+k+32≤R₀+182 by omega)
    · exact Real.rpow_le_rpow_of_exponent_le hN he'
    · exact Real.rpow_nonneg (by linarith) _
    · positivity
  by_cases hlow : lam≤9/10
  · refine ⟨6,by norm_num,by norm_num,by norm_num; linarith,?_⟩
    apply hfinish 6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one] using halasz_low_degree_saving hlo hlow
  · have hmed : 9/10≤lam := by linarith
    obtain ⟨hk,hd,hdk,hkl,hkh,hdl,hdh⟩ := halasz_medium_degree_bounds hmed
    have hk150 : halaszMediumDegree lam≤150 := by
      exact_mod_cast (show (halaszMediumDegree lam:ℝ)≤150 by linarith)
    refine ⟨halaszMediumDegree lam,hk,hk150,?_,?_⟩
    · have ht := halasz_small_taylor_exponent hkl
      linarith
    · apply hfinish (halaszMediumDegree lam) (halaszMediumActive lam) hk hk150 hd hdk
      exact halasz_medium_degree_saving hmed hhi (by positivity) hkh hdl hdh

end TwoPointCorrelations

end OAI
