import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogShiftBound
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTaylorScale

namespace OAI

/-! Uniform logarithmic phase prefixes from the normalized polynomial
estimate, with one common boundary error for both short-variable scales. -/
namespace TwoPointCorrelations

open Finset Complex

theorem halasz_phase_from_polynomial {N H k : ℕ} (hN : 1≤N) (hH : H≤N)
    {a t α lam A : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hα : 0≤α) (hαhi : α≤1/3)
    (hA : 0≤A) (hhalf : (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2) (ht : |t|=(N:ℝ)^lam)
    (htaylor : lam+(2*α-1)*((k:ℝ)+1)≤-(1/2:ℝ))
    (hpoly : ∀ z∈Set.Icc (N:ℝ) (2*N),
      ‖∑ b : Fin (halaszShortScale N α),halaszVinogradovPolynomial k (halaszShortScale N α)
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(halaszShortScale N α:ℝ)^2≤A) :
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log ((N:ℝ)+a+n):ℝ):ℂ))‖≤
      (N:ℝ)*A+4*(N:ℝ)^(2/3:ℝ) := by
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  let M := halaszShortScale N α
  have hM := (halasz_short_scale_bounds hNR hα).1
  have hM2 : (M:ℝ)^2≤(N:ℝ)^(2*α) := halasz_short_scale_square hNR hα
  have hM23 : (M:ℝ)^2≤(N:ℝ)^(2/3:ℝ) := hM2.trans
    (Real.rpow_le_rpow_of_exponent_le hNR (by linarith))
  have hMx : (M:ℝ)^2≤((N:ℝ)+a)/2 := by linarith [ha.1]
  have hx : 0<(N:ℝ)+a := by linarith [ha.1]
  have h := halasz_log_shift_bound k H M hM t hx hMx (A := A) (fun n hn => by
    apply hpoly
    have hnN : n+1≤N := by have := mem_range.mp hn; omega
    have hnNR : (n:ℝ)+1≤N := by exact_mod_cast hnN
    exact ⟨by linarith [ha.1,show (0:ℝ)≤n from Nat.cast_nonneg n],by linarith [ha.2]⟩)
  have he := halasz_taylor_scale hNR (show (N:ℝ)≤(N:ℝ)+a by linarith [ha.1]) hM2 ht htaylor
  have hHR : (H:ℝ)≤N := by exact_mod_cast hH
  have herr : (H:ℝ)*(2*(N:ℝ)^(-(1/2:ℝ)))≤2*(N:ℝ)^(2/3:ℝ) := by
    calc
      _ ≤ (N:ℝ)*(2*(N:ℝ)^(-(1/2:ℝ))) :=
        mul_le_mul_of_nonneg_right hHR (by positivity)
      _ = 2*((N:ℝ)^(1:ℝ)*(N:ℝ)^(-(1/2:ℝ))) := by rw [Real.rpow_one]; ring
      _ = 2*(N:ℝ)^(1/2:ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNR (by norm_num : (1/2:ℝ)≤2/3)) (by norm_num)
  apply h.trans
  have hmain := mul_le_mul_of_nonneg_right hHR hA
  have herror := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg H)
  nlinarith

end TwoPointCorrelations

end OAI
