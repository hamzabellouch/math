import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Estimates.TwoAdicQuadratic
import OAI.NumberTheory.Catalan.Polynomial.CentralCoefficients

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial

def reversedRow (C : ℕ) (F : ℤ[X]) : ℤ[X] :=
  ∑ u ∈ Finset.range C, Polynomial.C (F.coeff u) * X ^ (C - 1 - u)

def rowP (N r : ℕ) : ℤ[X] :=
  (1 - X) ^ h N *
    reversedRow (Cdegree N) (Polynomial.Chebyshev.T ℤ (rowDistance N r : ℤ))

def rowD (N r : ℕ) : ℤ[X] :=
  Polynomial.C (Int.sign (rowOffset N r)) * (1 - X) ^ h N *
    reversedRow (Cdegree N)
      (Polynomial.Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))

@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]

theorem reversedRow_coeff (C : ℕ) (F : ℤ[X]) (i : ℕ) :
    (reversedRow C F).coeff i = if i < C then F.coeff (C - 1 - i) else 0 := by
  classical
  unfold reversedRow
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hi : i < C
  · rw [ite_eq_left hi, Finset.sum_eq_single (C - 1 - i)]
    · rw [ite_eq_left (by omega : i = C - 1 - (C - 1 - i))]
    · intro u hu hne
      have hu' := Finset.mem_range.mp hu
      rw [ite_eq_right (by omega : i ≠ C - 1 - u)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [ite_eq_right (by omega : i ≠ C - 1 - u)]

theorem reversedRow_coeff_eq_zero_of_ge (C : ℕ) (F : ℤ[X])
    {i : ℕ} (hi : C ≤ i) : (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, ite_eq_right (by omega)]

theorem reversedRow_natDegree_le (C : ℕ) (F : ℤ[X]) :
    (reversedRow C F).natDegree ≤ C - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply reversedRow_coeff_eq_zero_of_ge
  omega

theorem reversedRow_coeff_eq_zero_of_lt (C d : ℕ) (F : ℤ[X])
    (hF : F.natDegree ≤ d) (hd : d < C) {i : ℕ} (hi : i < C - 1 - d) :
    (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, ite_eq_left (by omega)]
  apply coeff_eq_zero_of_natDegree_lt
  omega

theorem coeff_mul_eq_zero_below_right (P Q : ℤ[X]) (B : ℕ)
    (hQ : ∀ i < B, Q.coeff i = 0) {k : ℕ} (hk : k < B) :
    (P * Q).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.mem_antidiagonal.mp hij
  rw [hQ j (by omega), mul_zero]

theorem natDegree_one_sub_X : (1 - X : ℤ[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_sub]
  simpa using (Polynomial.natDegree_X_sub_C (1 : ℤ))

theorem rowFactor_natDegree_le (N : ℕ) :
    ((1 - X : ℤ[X]) ^ h N).natDegree ≤ h N := by
  calc
    _ ≤ h N * (1 - X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ = h N := by rw [InternalCatalan.natDegree_one_sub_X, mul_one]

theorem rowP_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowP N r).natDegree ≤ H N - 1 := by
  unfold rowP
  calc
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega

theorem rowD_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowD N r).natDegree ≤ H N - 1 := by
  unfold rowD
  rw [mul_assoc]
  calc
    _ ≤ (((1 - X : ℤ[X]) ^ h N) *
        reversedRow (Cdegree N) (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N)
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega

theorem rowP_coeff_eq_zero_of_lt {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hi : i < A N) : (rowP N r).coeff i = 0 := by
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (A N) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_Cdegree hN hr
  · exact lt_of_lt_of_le hj (A_le_reversed_T_min hN hr)

theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]

theorem rowD_coeff_eq_zero_of_lt {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hi : i < A N + 1) : (rowD N r).coeff i = 0 := by
  by_cases hd : rowDistance N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (A N + 1) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdist := rowDistance_lt_Cdegree hN hr
      omega
    · exact lt_of_lt_of_le hj (A_add_one_le_reversed_U_min hN hr (by omega))

theorem rowP_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowP N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowP_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega

theorem rowD_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowD N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowD_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega

theorem rowP_support {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    (rowP N r).support ⊆ Finset.Icc (A N) (H N - 1) := by
  intro i hi
  have hci := Polynomial.mem_support_iff.mp hi
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hb
    exact hci (rowP_coeff_eq_zero_of_lt hN hr (by omega))
  · by_contra hb
    exact hci (rowP_coeff_eq_zero_of_ge hN (by omega))

theorem rowD_support {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    (rowD N r).support ⊆ Finset.Icc (A N + 1) (H N - 1) := by
  intro i hi
  have hci := Polynomial.mem_support_iff.mp hi
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hb
    exact hci (rowD_coeff_eq_zero_of_lt hN hr (by omega))
  · by_contra hb
    exact hci (rowD_coeff_eq_zero_of_ge hN (by omega))

def realPoly (F : ℤ[X]) : ℝ[X] := F.map (Int.castRingHom ℝ)

def filteredColumn (N k : ℕ) : ℝ[X] := X ^ (b N + k) * (1 - X) ^ q N

def mixedMoment (P Q : ℝ[X]) : ℝ :=
  ∫ t in (-1 : ℝ)..1, ∫ s in (0 : ℝ)..1,
    (|t| / Real.sqrt (1 - t ^ 2)) * (P.eval t * Q.eval s) / (1 - t * s)

def zetaMoment (P Q : ℝ[X]) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
    (P.eval t * Q.eval s) / (1 - t * s)

def determinantEntry (N r k : ℕ) : ℝ :=
  mixedMoment (realPoly (rowP N r)) (filteredColumn N k) -
    (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) (filteredColumn N k)

def determinant (N : ℕ) : ℝ :=
  Matrix.det (fun r k : Fin (n N) => determinantEntry N r.val k.val)

def normalizedLog (N : ℕ) : ℝ :=
  Real.log |determinant N| / (n N : ℝ) ^ 2 - (1 / 2 : ℝ) * Real.log 2

def finiteLowerConstant : ℝ :=
  -(8609 / 4608 : ℝ) - ((1 / 2 : ℝ) + 505 / 4608) * Real.log 2

def realUpperConstant : ℝ := -(2290939875 / 1000000000 : ℝ)

def contradictionThreshold : ℝ := -(229087 / 100000 : ℝ)

theorem fixedTyped_reversedRow_add (F G : ℤ[X]) :
    reversedRow 63 (F + G) = reversedRow 63 F + reversedRow 63 G := by
  ext i
  simp only [reversedRow_coeff, coeff_add]
  split_ifs <;> simp

theorem fixedTyped_reversedRow_monomial (c : ℤ) (k : ℕ) (hk : k < 63) :
    reversedRow 63 (Polynomial.monomial (R := ℤ) k c) =
      Polynomial.monomial (R := ℤ) (62 - k) c := by
  ext i
  simp only [reversedRow_coeff, coeff_monomial]
  split_ifs <;> omega

theorem fixedTyped_rowFactor (p : ℤ[X]) :
    (1 - X) ^ 2 * p = p - 2 * (X * p) + X * (X * p) := by
  ring

theorem fixedTyped_rowP_of_parameters (N r exponent cutoff : ℕ) (index : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hi : (rowDistance N r : ℤ) = index) (hF : Chebyshev.T ℤ index = F) :
    rowP N r = (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowP
  rw [hh, hC, hi, hF]

theorem fixedTyped_rowD_of_parameters (N r exponent cutoff : ℕ) (index sign : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hs : Int.sign (rowOffset N r) = sign)
    (hi : (rowDistance N r : ℤ) - 1 = index) (hF : Chebyshev.U ℤ index = F) :
    rowD N r = Polynomial.C sign * (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowD
  rw [hh, hC, hs, hi, hF]

theorem fixed_rowDistance_le44 (r : Fin 49) : rowDistance 1 r.val ≤ 44 := by
  have hr := r.isLt
  unfold rowDistance rowOffset g
  omega

theorem fixed_rowP_coeff_eq_zero_below18 (r : Fin 49) {i : ℕ} (hi : i < 18) :
    (rowP 1 r.val).coeff i = 0 := by
  have hdist := fixed_rowDistance_le44 r
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ 18 _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val) _
  · simp [Chebyshev.natDegree_T]
  · change rowDistance 1 r.val < 63
    omega
  · change j < 63 - 1 - rowDistance 1 r.val
    omega

theorem fixed_rowD_coeff_eq_zero_below19 (r : Fin 49) {i : ℕ} (hi : i < 19) :
    (rowD 1 r.val).coeff i = 0 := by
  by_cases hd : rowDistance 1 r.val = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := fixed_rowDistance_le44 r
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ 19 _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val - 1) _
    · simp [Chebyshev.natDegree_U]
    · change rowDistance 1 r.val - 1 < 63
      omega
    · change j < 63 - 1 - (rowDistance 1 r.val - 1)
      omega

end

section

open scoped BigOperators

def rawEntryRat (z : ℚ) (N r j : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) *
    (momentRat i j + 4 * z * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) -
  (3 / 2 : ℚ) *
    ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j

def filterCoeffRat (N v : ℕ) : ℚ := (-1 : ℚ) ^ v * ((q N).choose v : ℚ)

def filteredEntryRat (z : ℚ) (N r k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (q N + 1),
    filterCoeffRat N v * rawEntryRat z N r (b N + k + v)

def determinantRat (z : ℚ) (N : ℕ) : ℚ :=
  Matrix.det (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val)

def fixedBaseEntryRat (r : Fin 49) (k : Fin 48) : ℚ :=
  filteredEntryRat 0 1 r.val k.val

theorem rawEntryRat_zero (N r j : ℕ) :
    rawEntryRat 0 N r j =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) * momentRat i j) -
      (3 / 2 : ℚ) *
        ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j := by
  simp [rawEntryRat]

def rawCatalanCoeffRat (N r j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (H N),
    ((rowP N r).coeff i : ℚ) * (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))

theorem rawEntryRat_affine (z : ℚ) (N r j : ℕ) :
    rawEntryRat z N r j = rawEntryRat 0 N r j + z * rawCatalanCoeffRat N r j := by
  unfold rawEntryRat rawCatalanCoeffRat
  simp only [mul_zero, zero_mul, add_zero]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) *
        (4 * z * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) =
      ∑ i ∈ Finset.range (H N), z *
        (((rowP N r).coeff i : ℚ) * (4 * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, ← Finset.mul_sum]
  ring

end

section

open Polynomial

theorem rowDistance_of_le_g {N r : ℕ} (hrg : r ≤ g N) :
    rowDistance N r = g N - r := by
  unfold rowDistance rowOffset
  omega

theorem rowP_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N - 1) :
    (rowP N r).coeff i = 0 := by
  have hdist := rowDistance_of_le_g hrg
  have hmin : L N - 1 ≤ Cdegree N - 1 - rowDistance N r := by
    rw [hdist]
    unfold L Cdegree g
    omega
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (L N - 1) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_Cdegree hN hr
  · exact lt_of_lt_of_le hj hmin

theorem rowD_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N) :
    (rowD N r).coeff i = 0 := by
  by_cases hd : rowDistance N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := rowDistance_of_le_g hrg
    have hmin : L N ≤ Cdegree N - 1 - (rowDistance N r - 1) := by
      rw [hdist]
      rw [hdist] at hd
      unfold L Cdegree g at *
      omega
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (L N) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdc := rowDistance_lt_Cdegree hN hr
      omega
    · exact lt_of_lt_of_le hj hmin

theorem row_contact_of_le_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rw [rowD_coeff_eq_zero_of_lt_left_contact hN hr hrg hj, Int.cast_zero]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hil : i < L N - 1
  · rw [rowP_coeff_eq_zero_of_lt_left_contact hN hr hrg hil, Int.cast_zero, zero_mul]
  · rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]

theorem polynomial_support_subset_range {F : ℤ[X]} {C : ℕ}
    (hF : F.natDegree < C) : F.support ⊆ Finset.range C := by
  intro i hi
  apply Finset.mem_range.mpr
  exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hi)) hF

theorem polynomial_eq_sum_range {F : ℤ[X]} {C : ℕ} (hF : F.natDegree < C) :
    F = ∑ u ∈ Finset.range C, Polynomial.C (F.coeff u) * X ^ u := by
  calc
    F = F.sum (fun u a => Polynomial.C a * X ^ u) := (sum_C_mul_X_pow_eq F).symm
    _ = _ := sum_eq_of_subset (fun u a => Polynomial.C a * X ^ u)
      (by intro u; simp) (polynomial_support_subset_range hF)

variable {K : Type*} [Field K]

theorem reversedRow_eval₂ (f : ℤ →+* K) {C : ℕ} {F : ℤ[X]}
    (hF : F.natDegree < C) {x : K} (hx : x ≠ 0) :
    (reversedRow C F).eval₂ f x = x ^ (C - 1) * F.eval₂ f x⁻¹ := by
  classical
  have hev : F.eval₂ f x⁻¹ =
      ∑ u ∈ Finset.range C, f (F.coeff u) * (x⁻¹) ^ u := by
    rw [eval₂_eq_sum]
    exact sum_eq_of_subset (fun u a => f a * (x⁻¹) ^ u)
      (by intro u; simp) (polynomial_support_subset_range hF)
  rw [hev, Finset.mul_sum]
  unfold reversedRow
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  have hpow : x ^ (C - 1) = x ^ (C - 1 - u) * x ^ u := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, inv_pow]
  field_simp [hx]

theorem rowP_eval₂ (f : ℤ →+* K) {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) {x : K} (hx : x ≠ 0) :
    (rowP N r).eval₂ f x =
      (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.T ℤ (rowDistance N r : ℤ)).eval₂ f x⁻¹ := by
  have hT : (Chebyshev.T ℤ (rowDistance N r : ℤ)).natDegree < Cdegree N := by
    simpa [Chebyshev.natDegree_T] using rowDistance_lt_Cdegree hN hr
  unfold rowP
  rw [eval₂_mul, reversedRow_eval₂ f hT hx]
  simp only [eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  exact (mul_assoc _ _ _).symm

theorem rowD_eval₂ (f : ℤ →+* K) {N r : ℕ} (hN : 0 < N)
    (hr : r < n N) {x : K} (hx : x ≠ 0) :
    (rowD N r).eval₂ f x =
      f (Int.sign (rowOffset N r)) * (1 - x) ^ h N * x ^ (Cdegree N - 1) *
        (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ f x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).natDegree < Cdegree N := by
    have hd := rowDistance_lt_Cdegree hN hr
    rw [Chebyshev.natDegree_U]
    simp only [sub_add_cancel, Int.natAbs_natCast]
    omega
  unfold rowD
  rw [eval₂_mul, eval₂_mul, reversedRow_eval₂ f hU hx]
  simp only [eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  ring

end

open Polynomial

theorem filteredColumn_det_eq_vandermonde (N : ℕ) (s : Fin (n N) → ℝ) :
    Matrix.det (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
      Matrix.det (Matrix.vandermonde s) *
        ∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N := by
  classical
  have hmatrix :
      (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
        Matrix.of (fun j k : Fin (n N) =>
          ((s j) ^ b N * (1 - s j) ^ q N) * Matrix.vandermonde s j k) := by
    funext j k
    simp only [filteredColumn, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
      Matrix.of_apply, Matrix.vandermonde_apply, pow_add]
    ring
  rw [hmatrix, Matrix.det_mul_column]
  exact mul_comm _ _

theorem filteredColumn_det_eq_prod (N : ℕ) (s : Fin (n N) → ℝ) :
    Matrix.det (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)) =
      (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) *
        ∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N := by
  rw [filteredColumn_det_eq_vandermonde, Matrix.det_vandermonde]

end InternalCatalan

end

end OAI
