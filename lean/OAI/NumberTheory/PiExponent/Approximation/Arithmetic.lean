import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

namespace OAI

namespace PiExponent.Arithmetic

noncomputable def lcmConstant : ℝ := Real.log 4 + 4

theorem lcmConstant_pos : 0 < lcmConstant := by
  have h : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  dsimp [lcmConstant]
  linarith

theorem log_lcmUpto_le (n : ℕ) :
    Real.log (Nat.lcmUpto n : ℝ) ≤ lcmConstant * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem gaussian_norm_one_le (z : GaussianInt) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℂ)‖ := by
  have hi : (1 : ℤ) ≤ z.norm := (GaussianInt.norm_pos.mpr hz)
  have hr : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hr
  have hn : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  nlinarith

theorem gaussian_det_norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι GaussianInt) (hA : A.det ≠ 0) :
    1 ≤ ‖(A.map GaussianInt.toComplex).det‖ := by
  change 1 ≤ ‖(GaussianInt.toComplex.mapMatrix A).det‖
  rw [← RingHom.map_det]
  exact gaussian_norm_one_le A.det hA

theorem det_row_column_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℂ) :
    Matrix.det (fun i j => r i * (c j * A i j)) =
      (∏ i, r i) * (∏ j, c j) * A.det := by
  calc
    _ = (∏ i, r i) * (Matrix.of fun i j => c j * A i j).det :=
      Matrix.det_mul_column r (Matrix.of fun i j => c j * A i j)
    _ = _ := by rw [Matrix.det_mul_row c A]; ring

theorem cleared_det_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    1 ≤ (∏ i, r i) * (∏ j, c j) * ‖A.det‖ := by
  have hd : (B.map GaussianInt.toComplex).det =
      (∏ i, (r i : ℂ)) * (∏ j, (c j : ℂ)) * A.det := by
    rw [hB, det_row_column_scale]
  have hn : B.det ≠ 0 := by
    intro he
    have hz : (B.map GaussianInt.toComplex).det = 0 := by
      change (GaussianInt.toComplex.mapMatrix B).det = 0
      rw [← RingHom.map_det, he, map_zero]
    rw [hd] at hz
    have hr' : (∏ i, (r i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact_mod_cast (hr i).ne')
    have hc' : (∏ j, (c j : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact_mod_cast (hc j).ne')
    exact mul_ne_zero (mul_ne_zero hr' hc') hA hz
  have h := gaussian_det_norm_one_le B hn
  rw [hd, norm_mul, norm_mul, norm_prod, norm_prod] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr _),
    abs_of_pos (hc _)] using h

theorem cleared_det_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : Matrix ι ι GaussianInt)
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map GaussianInt.toComplex = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j)) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have hrp : 0 < ∏ i, r i := Finset.prod_pos (by intro i hi; exact hr i)
  have hcp : 0 < ∏ i, c i := Finset.prod_pos (by intro i hi; exact hc i)
  have hn : 0 < ‖A.det‖ := norm_pos_iff.mpr hA
  have h := Real.log_nonneg (cleared_det_norm_bound A B r c hr hc hA hB)
  rw [Real.log_mul (mul_pos hrp hcp).ne' hn.ne', Real.log_mul hrp.ne' hcp.ne',
    Real.log_prod (by intro i hi; exact (hr i).ne'),
    Real.log_prod (by intro i hi; exact (hc i).ne')] at h
  linarith

theorem log_lcm_power_product_le {ι : Type*} (s : Finset ι) (T e : ι → ℕ) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ e i) ≤
      lcmConstant * ∑ i ∈ s, (e i : ℝ) * T i := by
  rw [Real.log_prod (by intro i hi; exact pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero (T i)))]
  simp_rw [Real.log_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (log_lcmUpto_le (T i)) (Nat.cast_nonneg (e i) : (0 : ℝ) ≤ e i)
  nlinarith only [h]

theorem log_lcm_floor_product_le {ι : Type*} (s : Finset ι)
    (T : ι → ℕ) (w : ι → ℝ) (H : ℝ) (hH : 0 ≤ H) (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / w i⌋₊) ≤
      H * lcmConstant * ∑ i ∈ s, (T i : ℝ) / w i := by
  calc
    _ ≤ lcmConstant * ∑ i ∈ s, (⌊H / w i⌋₊ : ℝ) * T i :=
      log_lcm_power_product_le s T _
    _ ≤ lcmConstant * ∑ i ∈ s, (H / w i) * T i := by
      apply mul_le_mul_of_nonneg_left _ lcmConstant_pos.le
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (T i))
      exact Nat.floor_le (div_nonneg hH (hw i hi).le)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sum_ceil_truncation_div_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i) ≤
      F * s.card / v + ∑ i ∈ s, 1 / w i := by
  calc
    _ ≤ ∑ i ∈ s, (F * w i / v + 1) / w i := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (hw i hi).le
      exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (hw i hi).le) hv.le)).le
    _ = ∑ i ∈ s, (F / v + 1 / w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hw i hi).ne', hv.ne']
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const]; simp; ring

theorem truncation_denominator_log_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v H : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hH : 0 < H)
    (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s,
      (Nat.lcmUpto (⌈F * w i / v⌉₊) : ℝ) ^ ⌊H / w i⌋₊) / H ≤
      lcmConstant * F * s.card / v + lcmConstant * ∑ i ∈ s, 1 / w i := by
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ H * lcmConstant * ∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i :=
      log_lcm_floor_product_le s _ w H hH.le hw
    _ ≤ H * lcmConstant * (F * s.card / v + ∑ i ∈ s, 1 / w i) := by
      exact mul_le_mul_of_nonneg_left (sum_ceil_truncation_div_le s w F v hF hv hw)
        (mul_pos hH lcmConstant_pos).le
    _ = _ := by ring

theorem dvd_lcmUpto_of_pos_le {k T : ℕ} (hk : 0 < k) (hkT : k ≤ T) :
    k ∣ Nat.lcmUpto T := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, hkT⟩)

theorem lcm_mul_log_coeff_gaussian (T k : ℕ) (hk : k ≤ T) :
    (Nat.lcmUpto T : ℂ) * PowerSeries.coeff k (PowerSeries.log ℂ) ∈
      GaussianInt.toComplex.range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  obtain ⟨m, hm⟩ := dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  refine ⟨((-1 : GaussianInt) ^ (k + 1)) * (m : GaussianInt), ?_⟩
  rw [PowerSeries.coeff_log, ite_eq_right hk0, hm]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

theorem cleared_log_trunc_mem (T : ℕ) :
    Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  apply (Polynomial.mem_map_range GaussianInt.toComplex).mpr
  intro k
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact lcm_mul_log_coeff_gaussian T k hk.le
  · simp

theorem exists_cleared_log_trunc (T : ℕ) :
    ∃ P : Polynomial GaussianInt,
      P.map GaussianInt.toComplex =
        Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) :=
  cleared_log_trunc_mem T

theorem gaussian_C_mem (z : GaussianInt) :
    Polynomial.C (z : ℂ) ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  exact ⟨Polynomial.C z, by simp⟩

theorem cleared_shifted_log_trunc_mem (T q : ℕ) (z : GaussianInt) :
    Polynomial.C (Nat.lcmUpto T : ℂ) *
      (Polynomial.C (z : ℂ) + Polynomial.C (q : ℂ) *
        PowerSeries.trunc T (PowerSeries.log ℂ)) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (Nat.lcmUpto T : ℂ) ∈ S := by
    simp
  have hq : Polynomial.C (q : ℂ) ∈ S := by
    simp
  have hlog := cleared_log_trunc_mem T
  have h := S.add_mem (S.mul_mem hL (gaussian_C_mem z)) (S.mul_mem hq hlog)
  convert h using 1
  ring

theorem cleared_polynomial_power_mem (L e d : ℕ) (f : Polynomial ℂ) (hd : d ≤ e)
    (hf : Polynomial.C (L : ℂ) * f ∈ (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C ((L : ℂ) ^ e) * f ^ d ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hL : Polynomial.C (L : ℂ) ∈ S := by
    simp
  have h := S.mul_mem (S.pow_mem hL (e - d)) (S.pow_mem hf d)
  have he : e = (e - d) + d := (Nat.sub_add_cancel hd).symm
  rw [he, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_polynomial_product_mem {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) :
    Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * (∏ i ∈ s, f i ^ d i) ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have h := S.prod_mem (fun i hi => cleared_polynomial_power_mem (L i) (e i) (d i)
    (f i) (hd i hi) (hf i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

theorem common_denominator_coeff_gaussian {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial ℂ) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : ℂ) * f i ∈
      (Polynomial.mapRingHom GaussianInt.toComplex).range) (k : ℕ) :
    (∏ i ∈ s, (L i : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  let S := (Polynomial.mapRingHom GaussianInt.toComplex).range
  have hP : P.map GaussianInt.toComplex ∈ S := ⟨P, rfl⟩
  have h := S.mul_mem hP (cleared_polynomial_product_mem s L e d f hd hf)
  have he : P.map GaussianInt.toComplex *
      (Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) * ∏ i ∈ s, f i ^ d i) =
      Polynomial.C (∏ i ∈ s, (L i : ℂ) ^ e i) *
        (P.map GaussianInt.toComplex * ∏ i ∈ s, f i ^ d i) := by ring
  rw [he] at h
  have hc := (Polynomial.mem_map_range GaussianInt.toComplex).mp h k
  simpa only [Polynomial.coeff_C_mul] using hc

theorem cleared_det_log_bound_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hentries : ∀ i j, (r i : ℂ) * ((c j : ℂ) * A i j) ∈ GaussianInt.toComplex.range) :
    -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  classical
  choose B hB using hentries
  apply cleared_det_log_bound A B r c hr hc hA
  ext i j
  exact hB i j

theorem cleared_det_log_bound_with_denominator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (r c : ι → ℝ) (D : ℝ)
    (hD : 0 < D) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i) (hA : A.det ≠ 0)
    (hentries : ∀ i j, (D : ℂ) * (r i : ℂ) * ((c j : ℂ) * A i j) ∈
      GaussianInt.toComplex.range) :
    -(Fintype.card ι : ℝ) * Real.log D - (∑ i, Real.log (r i)) -
      ∑ j, Real.log (c j) ≤ Real.log ‖A.det‖ := by
  have h := cleared_det_log_bound_of_entries A (fun i => D * r i) c
    (fun i => mul_pos hD (hr i)) hc hA (by simpa using hentries)
  simp_rw [Real.log_mul hD.ne' (hr _).ne'] at h
  rw [Finset.sum_add_distrib, Finset.sum_const] at h
  simp only [Finset.card_univ, nsmul_eq_mul] at h
  linarith

theorem shifted_truncation_product_coeff_gaussian {ι : Type*} (s : Finset ι)
    (T q e d : ι → ℕ) (z : ι → GaussianInt) (P : Polynomial GaussianInt)
    (hd : ∀ i ∈ s, d i ≤ e i) (k : ℕ) :
    (∏ i ∈ s, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (P.map GaussianInt.toComplex * ∏ i ∈ s,
        (Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
          PowerSeries.trunc (T i) (PowerSeries.log ℂ)) ^ d i).coeff k ∈
      GaussianInt.toComplex.range := by
  exact common_denominator_coeff_gaussian s (fun i => Nat.lcmUpto (T i)) e d _ P hd
    (fun i hi => cleared_shifted_log_trunc_mem (T i) (q i) (z i)) k

theorem column_log_cost_le {ι : Type*} (s : Finset ι) (a q : ι → ℕ) :
    (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) ≤
      ∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)

theorem sum_exponents_le_weight_div {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (w : ι → ℝ) (wmin : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ w i) :
    (∑ i ∈ s, (a i : ℝ)) ≤ (∑ i ∈ s, (a i : ℝ) * w i) / wmin := by
  apply (le_div_iff₀ hmin).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hw i hi) (Nat.cast_nonneg _))

theorem row_log_cost_lower {ι : Type*} (s : Finset ι)
    (a q : ι → ℕ) (wmin U : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ (⌈Real.log (q i)⌉₊ : ℝ))
    (hbudget : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤ U) :
    (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) - U / wmin ≤
      ∑ i ∈ s, (a i : ℝ) * Real.log (q i) := by
  have hsum := sum_exponents_le_weight_div s a (fun i => (⌈Real.log (q i)⌉₊ : ℝ))
    wmin hmin hw
  have hsumU : (∑ i ∈ s, (a i : ℝ)) ≤ U / wmin :=
    hsum.trans (div_le_div_of_nonneg_right hbudget hmin.le)
  have hceil : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤
      (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) + ∑ i ∈ s, (a i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (Nat.ceil_lt_add_one (Real.log_natCast_nonneg (q i))).le (Nat.cast_nonneg (a i) : (0 : ℝ) ≤ a i)
    nlinarith only [h]
  linarith

theorem normalized_arithmetic_bound (M H b E δ logD columnCost rowCost logAbsDet : ℝ)
    (hM : 0 < M) (hH : 0 < H)
    (hclear : -M * logD - columnCost + rowCost ≤ logAbsDet)
    (hden : logD ≤ H * E)
    (hcol : columnCost ≤ M * H)
    (hrow : M * H * b - M * H * δ ≤ rowCost) :
    -(1 - b) - (E + δ) ≤ logAbsDet / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hd := mul_le_mul_of_nonneg_left hden hM.le
  nlinarith only [hclear, hd, hcol, hrow]

end PiExponent.Arithmetic

end OAI
