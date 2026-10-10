import OAI.NumberTheory.TwoPointCorrelations.MRTCofactorWindow

namespace OAI

/-! A mean-square bound for the actual fixed-window cofactor polynomial.
The reciprocal-count weight is a contraction, so this estimate is uniform
in all remaining typical-factorization masks. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_cofactor_exponential_polynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    mrtCofactorPolynomial P F N a t =
      mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / a⌋₊ ⌊(2 * N : ℝ) / a⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtCofactorPolynomial
  rw [← sum_filter, mrt_cofactor_window_set N ha]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold mrtDirichletAtom
  ring

lemma mrt_reciprocal_count_oneBounded (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) :
    OneBounded (fun n => F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) := by
  intro n hn
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (finitePrimeDivisorCount P n + 1 : ℕ))).mpr
  exact (hF n hn).trans (by norm_num)

/-- The usual cofactor mean square, with its actual length `N/a`.
Neither the number nor the sizes of other prime bands enter the constant. -/
theorem mrt_cofactor_mean_square (P : Finset ℕ) (F : ℕ → ℂ)
    (hF : OneBounded F) (N : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N : ℝ) / a) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCofactorPolynomial P F N a t‖ ^ 2) ≤
      32 * Real.exp 1 * (T * a / (N : ℝ) + 1) := by
  let m := ⌊(N : ℝ) / a⌋₊
  let n := ⌊(2 * N : ℝ) / a⌋₊
  have ha0 : 0 < a := by linarith
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * a)
    ((le_div_iff₀ ha0).mp hx)
  obtain ⟨hm, hmn, _⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm
  change m ≤ n at hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlower : (N : ℝ) / a ≤ 2 * m := by
    have hfloor := Nat.lt_floor_add_one ((N : ℝ) / a)
    change (N : ℝ) / a < (m : ℝ) + 1 at hfloor
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hNm : (N : ℝ) ≤ 2 * a * m := by
    have hh := (div_le_iff₀ ha0).mp hlower
    nlinarith
  have hnR : (n : ℝ) ≤ 4 * m := by
    have hfloor := Nat.floor_le (show 0 ≤ (2 * N : ℝ) / a by positivity)
    change (n : ℝ) ≤ (2 * N : ℝ) / a at hfloor
    have he : (2 * N : ℝ) / a = 2 * ((N : ℝ) / a) := by ring
    rw [he] at hfloor
    linarith
  have hcoeff := mrt_reciprocal_count_oneBounded P F hF
  have hmass : (∑ k ∈ Ioc m n,
      ‖(F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)‖ ^ 2) ≤
      (m : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ k ∈ Ioc m n, ((k : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro k hk
        have hk0 : 0 < k := hm.trans (mem_Ioc.mp hk).1
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
        rw [norm_div, Complex.norm_natCast]
        calc
          _ ≤ (1 / (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity)
            (div_le_div_of_nonneg_right (hcoeff k hk0) hkR.le) 2
          _ = _ := by simp
      _ ≤ (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hm.ne' hmn
      _ ≤ _ := sub_le_self _ (by positivity)
  have hmean := mrt_dirichlet_mean_square_subset (Ioc m n)
    (N := n) (by intro k hk; exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega,
      (mem_Ioc.mp hk).2⟩)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ)) hT
  have hTm : T / (m : ℝ) ≤ 2 * (T * a / (N : ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    calc
      T = (T * (N : ℝ)) / N := by field_simp
      _ ≤ (T * (2 * a * m)) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNm hT.le) hNr.le
      _ = (2 * (T * a / (N : ℝ))) * m := by ring
  have hnm : (n : ℝ) / m ≤ 4 := (div_le_iff₀ hmR).mpr hnR
  simp_rw [mrt_cofactor_exponential_polynomial P F N ha]
  change (∫ t in -T..T, ‖mrtExponentialPolynomial (Ioc m n)
    (fun k => (F k / ((finitePrimeDivisorCount P k + 1 : ℕ) : ℂ)) / (k : ℂ))
    (fun k => -Real.log (k : ℝ)) t‖ ^ 2) ≤ _
  apply hmean.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (n : ℝ)) * (m : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 8 * Real.exp 1 * (T / (m : ℝ) + (n : ℝ) / m) := by ring
    _ ≤ 8 * Real.exp 1 * (2 * (T * a / (N : ℝ)) + 4) :=
      mul_le_mul_of_nonneg_left (add_le_add hTm hnm) (by positivity)
    _ ≤ _ := by
      have hp : 0 ≤ Real.exp 1 * (T * a / (N : ℝ)) := by positivity
      nlinarith

end TwoPointCorrelations

end OAI
