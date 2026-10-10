import OAI.NumberTheory.TwoPointCorrelations.MRTMixedPolynomial
import OAI.NumberTheory.TwoPointCorrelations.MRTShortEuler
import OAI.NumberTheory.TwoPointCorrelations.MRTCofactorMean

namespace OAI

/-! The mixed moment needed by the second and later MRT frequency classes.
This is the actual reciprocal-count cofactor, with arbitrary one-bounded
remaining masks. Its only loss is the explicit prime-tuple factorial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_short_prime_cofactor_moment (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 := by
  let M := Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊
  let B : ℕ → ℂ := fun n => F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)
  let U : ℕ := 2 ^ (r + 1) * Y * N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hM (m : ℕ) (hm : m ∈ M) : 0 < m := by
    have := (mem_Ioc.mp hm).1
    omega
  have hwindow (m : ℕ) (hm : m ∈ M) : (N : ℝ) < u * m ∧ u * m ≤ 2 * N := by
    change m ∈ Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊ at hm
    rw [← mrt_cofactor_window_set N hu] at hm
    exact (mem_filter.mp hm).2
  have hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      N < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U := by
    intro v hv m hm
    have hlo : Y ^ r ≤ ∏ i, v i := by
      calc
        _ = ∏ _i : Fin r, Y := by simp
        _ ≤ _ := prod_le_prod (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).1)
    have hhi : (∏ i, v i) ≤ (2 * Y) ^ r := by
      calc
        _ ≤ ∏ _i : Fin r, 2 * Y := prod_le_prod (fun i _ =>
          (mem_Icc.mp (hbin (Fintype.mem_piFinset.mp hv i))).2)
        _ = _ := by simp
    have hloR : u ≤ ((∏ i, v i : ℕ) : ℝ) := hpowlo.trans (by exact_mod_cast hlo)
    have hhiR : ((∏ i, v i : ℕ) : ℝ) ≤ (2 : ℝ) ^ r * u * Y := by
      calc
        _ ≤ ((2 : ℝ) * Y) ^ r := by exact_mod_cast hhi
        _ = (2 : ℝ) ^ r * (Y : ℝ) ^ r := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ r * (u * Y) :=
          mul_le_mul_of_nonneg_left hpowhi (by positivity)
        _ = _ := by ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hw := hwindow m hm
    constructor
    · have hh := hw.1.trans_le (mul_le_mul_of_nonneg_right hloR hm0)
      exact_mod_cast hh
    · have hh : ((∏ i, v i : ℕ) : ℝ) * m ≤
          (2 : ℝ) ^ (r + 1) * Y * N := by
        calc
          _ ≤ ((2 : ℝ) ^ r * u * Y) * m := mul_le_mul_of_nonneg_right hhiR hm0
          _ = ((2 : ℝ) ^ r * Y) * (u * m) := by ring
          _ ≤ ((2 : ℝ) ^ r * Y) * (2 * N) :=
            mul_le_mul_of_nonneg_left hw.2 (by positivity)
          _ = _ := by rw [pow_succ]; ring
      exact_mod_cast hh
  have hNU : N ≤ U := by
    have hp : 1 ≤ 2 ^ (r + 1) := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
    have hfactor : 1 ≤ 2 ^ (r + 1) * Y := one_le_mul_of_one_le_of_one_le hp hY
    simpa only [U, one_mul] using Nat.mul_le_mul_right N hfactor
  have hbound := mrt_mixed_prime_cofactor_mean_square P M hP hM a B ha
    (fun m hm => mrt_reciprocal_count_oneBounded Q F hF m (hM m hm))
    r hN hNU hsupport hT
  have he (t : ℝ) : mrtCofactorPolynomial Q F N u t =
      mrtExponentialPolynomial M (fun m => B m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t := mrt_cofactor_exponential_polynomial Q F N hu t
  simp_rw [he]
  apply hbound.trans
  have hratio : (T + (U : ℝ)) / (N : ℝ) =
      T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y := by
    dsimp [U]
    push_cast
    field_simp [hNR.ne']
  rw [hratio]
  calc
    _ ≤ 16 * Real.exp 1 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2 * Real.exp 9 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_euler_cube P hP hY hbin) (by positivity)
    _ = _ := by
      rw [show Real.exp 10 = Real.exp 1 * Real.exp 9 by rw [← Real.exp_add]; norm_num]
      ring

end TwoPointCorrelations

end OAI
