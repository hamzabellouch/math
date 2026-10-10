import OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeLogPolynomial
import OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentConstant
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSelection

namespace OAI

/-! Polynomial phase cancellation after removing the selected-moment
constant. The remaining loss is a fixed sixth power. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_large_log_polynomial_saving : ∃ R₀ : ℕ, ∀ m : ℕ, 8≤m →
    ∀ M : ℕ, 1≤M → ∀ t z N lam : ℝ, (M:ℝ)≤N → N≤z → z≤2*N →
    |t|=N^lam → N^(1/4:ℝ)≤2*(M:ℝ) → 6*(m:ℝ)-6≤lam → lam≤6*m →
    ‖∑ b : Fin M,halaszVinogradovPolynomial (12*m) M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      (R₀+12*m+32:ℝ)^6*N^(-1/((10^8:ℝ)*lam^2)) := by
  obtain ⟨R₀,hR⟩ := halasz_large_log_polynomial
  refine ⟨R₀,?_⟩
  intro m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  have h := hR m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  have hC := halasz_moment_constant_root (k := 12*m) (by omega) R₀
  push_cast at hC
  have hN : 1≤N := (show (1:ℝ)≤M by exact_mod_cast hM).trans hMN
  have hb := neg_le_neg (halasz_large_root_saving hm hlo)
  have he : -(m:ℝ)^2/(4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ)) ≤
      -1/((10^8:ℝ)*lam^2) := by simpa only [neg_div] using hb
  push_cast at h he
  exact h.trans (mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hN he)
    (Real.rpow_nonneg (by linarith) _) (by positivity))

theorem halasz_single_log_polynomial_saving : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k →
    ∀ M : ℕ, 1≤M → ∀ d : ℕ, 1≤d → d≤k → ∀ t z N lam q : ℝ,
    (M:ℝ)≤N → N≤z → z≤2*N → |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
    q+(k:ℝ)^2/1024≤min ((d:ℝ)/3) (min ((d:ℝ)-lam) (lam-(d:ℝ)/3)) →
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      (R₀+k+32:ℝ)^6*N^(-q/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)) := by
  obtain ⟨R₀,hR⟩ := halasz_selected_double_moment
  refine ⟨R₀,?_⟩
  intro k hk M hM d hd hdk t z N lam q hMN hz hzhi ht hscale hsave
  let r := halaszSelectedMoment k
  let p := 2*r*r
  let ε : ℝ := (k:ℝ)^2/1024
  let A := (32*(r:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)
  let D := (halaszLogWeightCost k r)^k
  have hr : 1≤r := halasz_selected_moment_pos hk
  have hp : 0<p := by dsimp only [p]; positivity
  have hN : 1≤N := (show (1:ℝ)≤M by exact_mod_cast hM).trans hMN
  have hN0 : 0<N := by linarith
  have ht0 : t≠0 := by
    intro ht0
    have hpos := Real.rpow_pos_of_pos hN0 lam
    rw [ht0,abs_zero] at ht
    linarith
  have hz0 : z≠0 := by linarith
  have hbase := hR k hk M hM (halaszLogCoefficient t z)
    (halasz_log_coefficient_ne_zero ht0 hz0)
  have hw := halasz_single_degree_weight_product hr hM hd hdk hN hz hzhi ht hscale
    (le_min_iff.mp hsave).1 (le_min_iff.mp (le_min_iff.mp hsave).2).1
    (le_min_iff.mp (le_min_iff.mp hsave).2).2
  have hh := hbase.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have hexp : 4*(r:ℝ)^2=((2*p:ℕ):ℝ) := by dsimp only [p]; push_cast; ring
  have hbound :
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^p ≤
        A*(M:ℝ)^(((2*p:ℕ):ℝ)+ε)*D*N^(-(q+ε)) := by
    convert hh using 1
    dsimp only [A,D,ε,r]
    rw [hexp]
    ring
  have hroot := halasz_moment_transfer hp (by positivity)
    (show 0≤A by dsimp only [A]; positivity)
    (show 0≤D by dsimp only [D]; exact pow_nonneg (halasz_log_weight_cost_pos _ _).le _)
    (show (1:ℝ)≤M by exact_mod_cast hM) hMN (by dsimp only [ε]; positivity)
    (show ε-(q+ε)≤-q by linarith) hbound
  exact hroot.trans (mul_le_mul_of_nonneg_right (halasz_moment_constant_root hk R₀)
    (Real.rpow_nonneg hN0.le _))

end TwoPointCorrelations

end OAI
