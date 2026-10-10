import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic
import OAI.NumberTheory.Catalan.Estimates.ChebyshevContact
import OAI.NumberTheory.Catalan.Estimates.MomentFilter
import OAI.NumberTheory.Catalan.Estimates.TwoAdicConvolution
import OAI.NumberTheory.Catalan.Estimates.TwoAdicSmoothingDecomposition

namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem rawColumn_card (N : ℕ) :
    Fintype.card ↥(Finset.Ico (b N) (L N)) = n N + q N := by
  simp only [Fintype.card_coe, Nat.card_Ico]
  rw [L_eq_n_add_b_add_q]
  omega

def rawMatrixRat (z : ℚ) (N : ℕ) :
    Matrix (Fin (n N)) ↥(Finset.Ico (b N) (L N)) ℚ :=
  fun r j => rawEntryRat z N r.val j.val

def rawFilterInt (N : ℕ) :
    Matrix ↥(Finset.Ico (b N) (L N)) (Fin (n N)) ℤ :=
  fun j k => filterCoeff N j.val k.val

theorem filteredEntryRat_eq_sum_contactRange (z : ℚ) (N r k : ℕ)
    (hk : k < n N) :
    filteredEntryRat z N r k =
      ∑ j ∈ Finset.Ico (b N) (L N),
        (filterCoeff N j k : ℚ) * rawEntryRat z N r j := by
  let F : ℤ[X] →ₗ[ℤ] ℚ :=
    Polynomial.lsum fun j => LinearMap.toSpanSingleton ℤ ℚ (rawEntryRat z N r j)
  have hF (j : ℕ) : F (X ^ j) = rawEntryRat z N r j := by
    simp [F, Polynomial.lsum_apply, Polynomial.X_pow_eq_monomial]
  calc
    filteredEntryRat z N r k = F (filteredColumnInt N k) := by
      rw [map_filteredColumnInt]
      simp only [hF, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
      rfl
    _ = _ := by
      simpa only [hF, zsmul_eq_mul] using
        (map_filteredColumnInt_contactRange F N k hk)

theorem filteredMatrixRat_eq_raw_mul_filter (z : ℚ) (N : ℕ) :
    (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val) =
      rawMatrixRat z N * (Matrix.of fun j k => (rawFilterInt N j k : ℚ)) := by
  ext r k
  rw [Matrix.mul_apply]
  simp only [rawMatrixRat, rawFilterInt, Matrix.of_apply]
  rw [Finset.sum_coe_sort (Finset.Ico (b N) (L N))
    (fun j : ℕ => rawEntryRat z N r.val j * (filterCoeff N j k.val : ℚ))]
  rw [filteredEntryRat_eq_sum_contactRange z N r.val k.val k.isLt]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem determinantRat_eq_det_raw_mul_filter (z : ℚ) (N : ℕ) :
    determinantRat z N =
      Matrix.det (rawMatrixRat z N * (Matrix.of fun j k => (rawFilterInt N j k : ℚ))) := by
  rw [determinantRat, filteredMatrixRat_eq_raw_mul_filter]

def rawMinorRat (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) : ℚ :=
  Matrix.det (Matrix.of fun r k : Fin (n N) => rawEntryRat z N r.val (c k).val)

theorem rawMinorRat_eq_zero_of_not_injective (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (hc : ¬Function.Injective c) : rawMinorRat z N c = 0 := by
  classical
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  unfold rawMinorRat
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply]
  rw [hij]

theorem determinantRat_eq_sum_raw_choices (z : ℚ) (N : ℕ) :
    determinantRat z N =
      ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)),
        ((∏ k : Fin (n N), rawFilterInt N (c k) k : ℤ) : ℚ) * rawMinorRat z N c := by
  classical
  rw [determinantRat_eq_det_raw_mul_filter]
  calc
    _ = ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)),
        ∑ σ : Equiv.Perm (Fin (n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k : Fin (n N),
            rawMatrixRat z N (σ k) (c k) * (rawFilterInt N (c k) k : ℚ) := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.of_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [rawMinorRat, rawMatrixRat, rawFilterInt]
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [Int.cast_prod, Finset.prod_mul_distrib, Matrix.of_apply]
      ring

theorem determinantRat_eq_sum_raw_minors (z : ℚ) (N : ℕ) :
    determinantRat z N =
      ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)) with Function.Injective c,
        ((∏ k : Fin (n N), rawFilterInt N (c k) k : ℤ) : ℚ) * rawMinorRat z N c := by
  classical
  rw [determinantRat_eq_sum_raw_choices]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hcinj
  have hnot : ¬Function.Injective c := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcinj
  rw [rawMinorRat_eq_zero_of_not_injective z N c hnot, mul_zero]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

def intPolynomialSeries (P : ℤ[X]) : PowerSeries ℚ :=
  (P.map (Int.castRingHom ℚ) : ℚ[X])

@[simp] theorem coeff_intPolynomialSeries (P : ℤ[X]) (j : ℕ) :
    PowerSeries.coeff j (intPolynomialSeries P) = (P.coeff j : ℚ) := by
  simp [intPolynomialSeries]

@[simp] theorem intPolynomialSeries_mul (P Q : ℤ[X]) :
    intPolynomialSeries (P * Q) = intPolynomialSeries P * intPolynomialSeries Q := by
  simp [intPolynomialSeries]

def contactSeries (P : ℤ[X]) : PowerSeries ℚ :=
  intPolynomialSeries P * (PowerSeries.X * centralKernelSeries)

theorem coeff_X_centralKernelSeries (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.X * centralKernelSeries) =
      centralCoeffKernel ((j : ℤ) - 1) := by
  cases j with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, Nat.cast_zero,
        centralCoeffKernel_of_neg (by norm_num : (0 : ℤ) - 1 < 0)]
  | succ j =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_centralKernelSeries]
      congr 1
      omega

theorem contactSeries_coeff_eq_sum (P : ℤ[X]) {B j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (contactSeries P) =
      ∑ i ∈ Finset.range B,
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
  unfold contactSeries
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => PowerSeries.coeff i (intPolynomialSeries P) *
        PowerSeries.coeff k (PowerSeries.X * centralKernelSeries)) j]
  calc
    _ = ∑ i ∈ Finset.range (j + 1),
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_intPolynomialSeries, coeff_X_centralKernelSeries]
      congr 2
      have hi' := Finset.mem_range.mp hi
      omega
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ B))
      intro i hi hin
      have hin' : ¬ i < j + 1 := by simpa only [Finset.mem_range] using hin
      rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]

theorem series_coeff_mul_congr_below {S T : PowerSeries ℚ} {B : ℕ}
    (hST : ∀ j < B, PowerSeries.coeff j S = PowerSeries.coeff j T)
    (Q : PowerSeries ℚ) {j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (Q * S) = PowerSeries.coeff j (Q * T) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨u, v⟩ huv
  have huv' : u + v = j := Finset.mem_antidiagonal.mp huv
  rw [hST v (by omega)]

theorem contactSeries_mul (P Q : ℤ[X]) :
    contactSeries (P * Q) = intPolynomialSeries P * contactSeries Q := by
  simp only [contactSeries, intPolynomialSeries_mul, mul_assoc]

theorem reversedChebyshev_contact_series {C d j : ℕ}
    (hd : d < C) (hj : j < C) :
    PowerSeries.coeff j
        (contactSeries (reversedRow C (Chebyshev.T ℤ (d : ℤ)))) =
      PowerSeries.coeff j
        (intPolynomialSeries (reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1)))) := by
  rw [contactSeries_coeff_eq_sum _ hj, coeff_intPolynomialSeries]
  exact reversedChebyshev_contact hd hj

theorem row_contact_of_gt_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : g N < r) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  have hjC : j < Cdegree N := by
    rw [Cdegree_eq_L_add_g]
    omega
  have hjH : j < H N := by
    rw [H_eq_Cdegree_add_h]
    omega
  have hd : rowDistance N r < Cdegree N := rowDistance_lt_Cdegree hN hr
  have hs : Int.sign (rowOffset N r) = 1 := by
    apply Int.sign_eq_one_of_pos
    unfold rowOffset
    omega
  have hbase : ∀ l < Cdegree N,
      PowerSeries.coeff l
          (contactSeries
            (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ)))) =
        PowerSeries.coeff l
          (intPolynomialSeries
            (reversedRow (Cdegree N)
              (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)))) := by
    intro l hl
    exact reversedChebyshev_contact_series hd hl
  have hmul := series_coeff_mul_congr_below hbase
    (intPolynomialSeries ((1 - X : ℤ[X]) ^ h N)) hjC
  rw [← contactSeries_mul, ← intPolynomialSeries_mul] at hmul
  rw [contactSeries_coeff_eq_sum _ hjH, coeff_intPolynomialSeries] at hmul
  simpa only [rowP, rowD, hs, Polynomial.C_1, one_mul] using hmul

theorem row_contact {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rcases le_or_gt r (g N) with hrg | hrg
  · exact row_contact_of_le_g hN hr hrg hj
  · exact row_contact_of_gt_g hN hr hrg hj

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def smoothingColumn (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (H N),
    ((rowP N r).coeff i : ℚ_[2]) * smoothingMoment i j

def exceptionColumn (q : ℚ) (N r j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ_[2]) *
        (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2])

def boundaryColumn (N r j : ℕ) : ℚ_[2] :=
  ∑ i ∈ Finset.range (H N),
    ((rowD N r).coeff i : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if i = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat i j : ℚ_[2]))

theorem rawEntryRat_two_adic_decomposition (q : ℚ) {N r j : ℕ}
    (hN : 0 < N) (hr : r < n N) (hj : j < L N) :
    (rawEntryRat q N r j : ℚ_[2]) =
      smoothingColumn N r j + exceptionColumn q N r j + boundaryColumn N r j := by
  classical
  have hjH : j < H N := by
    have hLH : L N ≤ H N := by unfold L H; omega
    exact lt_of_lt_of_le hj hLH
  have hcontact :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          (centralCoeffKernel ((j : ℤ) - i - 1) : ℚ_[2])) =
        ((rowD N r).coeff j : ℚ_[2]) := by
    exact_mod_cast row_contact hN hr hj
  have hdelta :
      (∑ i ∈ Finset.range (H N),
        ((rowD N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) =
        ((rowD N r).coeff j : ℚ_[2]) := by
    simp [Finset.mem_range, hjH]
  have hE :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        exceptionColumn q N r j := by
    unfold exceptionColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((-smoothingMoment 0 1) *
            (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]))) =
        (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) := by
    rw [← hcontact, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hentrysum :
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) =
        smoothingColumn N r j + exceptionColumn q N r j +
          (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) := by
    simp_rw [smoothingMoment_discrepancies q, mul_add, Finset.sum_add_distrib]
    rw [hE, hB]
    rfl
  have hboundary : boundaryColumn N r j =
      (-smoothingMoment 0 1) * ((rowD N r).coeff j : ℚ_[2]) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    unfold boundaryColumn
    calc
      _ = (-smoothingMoment 0 1) *
          (∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (if i = j then 1 else 0)) -
          (3 / 2 : ℚ_[2]) *
            ∑ i ∈ Finset.range (H N),
              ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hdelta]
  have hrawcast : (rawEntryRat q N r j : ℚ_[2]) =
      (∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℚ_[2]) *
          ((momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
            (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]))) -
        (3 / 2 : ℚ_[2]) *
          ∑ i ∈ Finset.range (H N),
            ((rowD N r).coeff i : ℚ_[2]) * (zetaRat i j : ℚ_[2]) := by
    simp only [rawEntryRat, Rat.cast_sub, Rat.cast_mul, Rat.cast_sum,
      Rat.cast_add, Rat.cast_ofNat, Rat.cast_div, Rat.cast_intCast]
  rw [hrawcast, hentrysum, hboundary]
  ring

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def rawColumnTerm (z : ℚ) (N r j : ℕ) (t : Fin 3) : ℚ_[2] :=
  if t = 0 then smoothingColumn N r j
  else if t = 1 then exceptionColumn z N r j
  else boundaryColumn N r j

theorem rawColumnTerm_sum (z : ℚ) (N r j : ℕ) :
    (∑ t : Fin 3, rawColumnTerm z N r j t) =
      smoothingColumn N r j + exceptionColumn z N r j + boundaryColumn N r j := by
  simp [Fin.sum_univ_succ, rawColumnTerm, add_assoc]

theorem rawMinorRat_cast_two_adic (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    (rawMinorRat z N c : ℚ_[2]) =
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        (rawEntryRat z N r.val (c k).val : ℚ_[2])) := by
  simp only [rawMinorRat, Matrix.det_apply', Matrix.of_apply, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_prod, Rat.cast_intCast]

theorem rawMinorRat_two_adic_column_expansion (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    (rawMinorRat z N c : ℚ_[2]) =
      ∑ τ : Fin (n N) → Fin 3,
        Matrix.det (Matrix.of fun r k : Fin (n N) =>
          rawColumnTerm z N r.val (c k).val (τ k)) := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => (rawEntryRat z N r.val (c k).val : ℚ_[2])) =
        (Matrix.of fun r k : Fin (n N) =>
          ∑ t : Fin 3, rawColumnTerm z N r.val (c k).val t) := by
    ext r k
    simp only [Matrix.of_apply, rawColumnTerm_sum]
    exact rawEntryRat_two_adic_decomposition z hN r.isLt
      (Finset.mem_Ico.mp (c k).property).2
  rw [rawMinorRat_cast_two_adic, hmatrix]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

theorem determinantRat_two_adic_column_expansion (z : ℚ) {N : ℕ} (hN : 0 < N) :
    (determinantRat z N : ℚ_[2]) =
      ∑ c : Fin (n N) → ↥(Finset.Ico (b N) (L N)) with Function.Injective c,
        ((∏ k : Fin (n N), rawFilterInt N (c k) k : ℤ) : ℚ_[2]) *
          ∑ τ : Fin (n N) → Fin 3,
            Matrix.det (Matrix.of fun r k : Fin (n N) =>
              rawColumnTerm z N r.val (c k).val (τ k)) := by
  classical
  rw [determinantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro c hc
  rw [rawMinorRat_two_adic_column_expansion z hN c]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem padic_two_norm_int_le_of_pow_dvd {z : ℤ} {e : ℕ}
    (hdiv : (2 : ℤ) ^ e ∣ z) : ‖(z : ℚ_[2])‖ ≤ 1 / (2 : ℝ) ^ e := by
  obtain ⟨w, rfl⟩ := hdiv
  push_cast
  rw [norm_mul, norm_pow]
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  rw [htwo]
  calc
    (1 / 2 : ℝ) ^ e * ‖(w : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ e * 1 :=
      mul_le_mul_of_nonneg_left (Padic.norm_int_le_one w) (by positivity)
    _ = 1 / (2 : ℝ) ^ e := by simp only [mul_one, one_div_pow]

theorem smoothingColumn_term_norm_le (N r i j : ℕ) (hi : i < H N) (hj : j < H N) :
    ‖((rowP N r).coeff i : ℚ_[2]) * smoothingMoment i j‖ ≤
      8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
  have hp := padic_two_norm_int_le_of_pow_dvd (rowP_coeff_two_pow_dvd N r i)
  have hm := smoothingMoment_norm_le_uniform (H N) i j hi hj
  have hexp : Cdegree N ≤ (Cdegree N - 2 - i) + i + 2 := by omega
  have hpow : (2 : ℝ) ^ Cdegree N ≤
      (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) * 4 := by
    calc
      (2 : ℝ) ^ Cdegree N ≤ (2 : ℝ) ^ (((Cdegree N - 2 - i) + i) + 2) :=
        pow_le_pow_right₀ (by norm_num) hexp
      _ = (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) * 4 := by
        rw [pow_add]
        norm_num
  rw [norm_mul]
  calc
    ‖((rowP N r).coeff i : ℚ_[2])‖ * ‖smoothingMoment i j‖ ≤
        (1 / (2 : ℝ) ^ (Cdegree N - 2 - i)) *
          (2 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ i) :=
      mul_le_mul hp hm (norm_nonneg _) (by positivity)
    _ = 2 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ ((Cdegree N - 2 - i) + i) := by
      rw [pow_add]
      ring
    _ ≤ 8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * (H N : ℝ) ^ 2)
      nlinarith only [hh]

theorem smoothingColumn_norm_le (N r j : ℕ) (hj : j < H N) :
    ‖smoothingColumn N r j‖ ≤ 8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
  unfold smoothingColumn
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  exact smoothingColumn_term_norm_le N r i j (Finset.mem_range.mp hi) hj







open scoped BigOperators

theorem padic_two_det_norm_le_prod_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[2]) (U : ι → ℝ) (hU : ∀ k, 0 ≤ U k)
    (hM : ∀ r k, ‖M r k‖ ≤ U k) :
    ‖Matrix.det M‖ ≤ ∏ k, U k := by
  classical
  rw [Matrix.det_apply']
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Finset.prod_nonneg (fun k hk => hU k))
  intro σ hσ
  rw [norm_mul, norm_prod]
  calc
    ‖((Equiv.Perm.sign σ : ℤ) : ℚ_[2])‖ * ∏ k, ‖M (σ k) k‖ ≤
        1 * ∏ k, U k := by
      apply mul_le_mul (Padic.norm_int_le_one (Equiv.Perm.sign σ))
      · exact Finset.prod_le_prod₀ (fun k hk => norm_nonneg _) (fun k hk => hM (σ k) k)
      · exact Finset.prod_nonneg (fun k hk => norm_nonneg _)
      · norm_num
    _ = ∏ k, U k := one_mul _

theorem smoothing_full_minor_norm_le (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) :
    ‖Matrix.det (fun r k : Fin (n N) => smoothingColumn N r.val (c k).val)‖ ≤
      (8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N) ^ n N := by
  have hentry (r k : Fin (n N)) :
      ‖smoothingColumn N r.val (c k).val‖ ≤
        8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N := by
    have hjL : (c k).val < L N := (Finset.mem_Ico.mp (c k).property).2
    have hLH : L N ≤ H N := by unfold L H; omega
    exact smoothingColumn_norm_le N r.val (c k).val (lt_of_lt_of_le hjL hLH)
  have hdet := padic_two_det_norm_le_prod_column
    (fun r k : Fin (n N) => smoothingColumn N r.val (c k).val)
    (fun _ => 8 * (H N : ℝ) ^ 2 / (2 : ℝ) ^ Cdegree N)
    (fun _ => by positivity) hentry
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hdet

end InternalCatalan

end

end OAI
