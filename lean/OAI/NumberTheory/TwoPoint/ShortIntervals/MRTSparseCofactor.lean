import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseMajorant
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMean

namespace OAI

/-! Sparse mean square with the actual reciprocal prime-count cofactor.
All coefficient and rounding normalizations are proved here. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

lemma mrt_cofactor_coefficient_square_mass (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) :
    (∑ k ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊,
      ‖(F k/((finitePrimeDivisorCount P k+1:ℕ):ℂ))/(k:ℂ)‖^2) ≤ 2*a/N := by
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hN : (0:ℝ) < N := by
    have hh := (le_div_iff₀ ha0).mp hx
    linarith
  obtain ⟨hm,hmn,_⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm
  change m ≤ n at hmn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlower : (N:ℝ)/a ≤ 2*m := by
    have hfloor := Nat.lt_floor_add_one ((N:ℝ)/a)
    change (N:ℝ)/a < (m:ℝ)+1 at hfloor
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  change (∑ k ∈ Ioc m n, _) ≤ _
  calc
    _ ≤ ∑ k ∈ Ioc m n, ((k:ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro k hk
      have hk0 := hm.trans (mem_Ioc.mp hk).1
      have hkR : (0:ℝ) < k := by exact_mod_cast hk0
      rw [norm_div, Complex.norm_natCast]
      calc
        _ ≤ (1/(k:ℝ))^2 := pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (hcoeff k hk0) hkR.le) 2
        _ = _ := by simp
    _ ≤ (m:ℝ)⁻¹-(n:ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hm.ne' hmn
    _ ≤ (m:ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ 2*a/N := by
      rw [inv_eq_one_div, div_le_iff₀ hm0]
      have hh := (div_le_iff₀ ha0).mp hlower
      calc
        (1:ℝ) = (N:ℝ)/N := by field_simp
        _ ≤ (2*a*m)/N := div_le_div_of_nonneg_right (by nlinarith) hN.le
        _ = _ := by ring

theorem mrt_sparse_cofactor_energy (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (hx : 2 ≤ (N:ℝ)/a)
    (K : Finset ℕ) (hK : Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊ ⊆ K)
    (w : ℕ → ℝ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (hw1 : ∀ n ∈ Ioc ⌊(N:ℝ)/a⌋₊ ⌊(2*N:ℝ)/a⌋₊, 1 ≤ w n)
    (S : Finset ℝ) (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ))
        (fun n => -Real.log (n:ℝ)) (t-s)‖ ≤ A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtCofactorPolynomial P F N a t‖^2) ≤
      (8*A+(S.card:ℝ)*D)*(2*a/N) := by
  simp_rw [mrt_cofactor_exponential_polynomial P F N ha]
  apply (mrt_sparse_majorized_energy K _ hK w (fun n => -Real.log (n:ℝ))
    (fun n => (F n/((finitePrimeDivisorCount P n+1:ℕ):ℂ))/(n:ℂ))
    hw hw1 S hsep hA hD hkernel).trans
  exact mul_le_mul_of_nonneg_left
    (mrt_cofactor_coefficient_square_mass P F hF N ha hx) (by positivity)

end TwoPointCorrelations

end OAI
