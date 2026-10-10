import OAI.NumberTheory.Catalan.Determinants.FixedClearedColumnsAll
import OAI.NumberTheory.Catalan.Polynomial.FixedBaseCertificateTransfer

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace InternalCatalan

def fixedIntegerBaseCanonical (r : Fin 49) (k : Fin 48) : ℤ :=
  2 * (∑ i ∈ Finset.range 65,
    (rowP 1 r.val).coeff i * fixedClearedMoment i k) -
  3 * (∑ i ∈ Finset.range 65,
    (rowD 1 r.val).coeff i * fixedClearedZeta i k)

private theorem integerFractionSum
    (s : Finset ℕ) (p a : ℕ → ℤ) (f : ℕ → ℚ) (d : ℚ)
    (hf : ∀ i ∈ s, (p i : ℚ) * f i = ((p i * a i : ℤ) : ℚ) / d) :
    (∑ i ∈ s, (p i : ℚ) * f i) = ((∑ i ∈ s, p i * a i : ℤ) : ℚ) / d := by
  rw [Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv] using hf i hi

theorem fixedRowP_filtered_integer_fraction (r : Fin 49) (k : Fin 48) :
    (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      fixedFilteredMomentRat i k.val) =
    ((∑ i ∈ Finset.range 65,
      (rowP 1 r.val).coeff i * fixedClearedMoment i k : ℤ) : ℚ) /
      427020799961118095468762173535463688638296295357889841725440000 := by
  apply integerFractionSum
  intro i hi
  have hhi : i < 65 := Finset.mem_range.mp hi
  by_cases hlo : 18 ≤ i
  · rw [fixedFilteredMoment_cleared i k hlo hhi, Int.cast_mul]
    ring
  · have hz := fixed_rowP_coeff_eq_zero_below18 r (i := i) (by omega)
    simp [hz]

theorem fixedRowD_filtered_integer_fraction (r : Fin 49) (k : Fin 48) :
    (∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      fixedFilteredZetaRat i k.val) =
    ((∑ i ∈ Finset.range 65,
      (rowD 1 r.val).coeff i * fixedClearedZeta i k : ℤ) : ℚ) /
      427020799961118095468762173535463688638296295357889841725440000 := by
  apply integerFractionSum
  intro i hi
  have hhi : i < 65 := Finset.mem_range.mp hi
  by_cases hlo : 19 ≤ i
  · rw [fixedFilteredZeta_cleared i k hlo hhi, Int.cast_mul]
    ring
  · have hz := fixed_rowD_coeff_eq_zero_below19 r (i := i) (by omega)
    simp [hz]

theorem fixedBaseEntry_integer_contraction (r : Fin 49) (k : Fin 48) :
    fixedBaseEntryRat r k =
      ((∑ i ∈ Finset.range 65,
        (rowP 1 r.val).coeff i * fixedClearedMoment i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 -
      (3 / 2 : ℚ) *
      (((∑ i ∈ Finset.range 65,
        (rowD 1 r.val).coeff i * fixedClearedZeta i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000) := by
  rw [fixedBaseEntry_dot_filtered,
    fixedRowP_filtered_integer_fraction, fixedRowD_filtered_integer_fraction]

theorem fixedIntegerBaseCanonical_cast (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ℚ) =
      (854041599922236190937524347070927377276592590715779683450880000 : ℚ) *
        fixedBaseEntryRat r k := by
  rw [fixedBaseEntry_integer_contraction]
  simp only [fixedIntegerBaseCanonical, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

theorem fixedCanonicalMatrix_integer_lift (sigma : ℤ) :
    (fixedIntegerMatrix fixedIntegerBaseCanonical sigma).map
      (fun x : ℤ => (x : ℚ)) =
      (854041599922236190937524347070927377276592590715779683450880000 : ℚ) •
        fixedMatrix (sigma : ℚ) :=
  fixedIntegerMatrix_cast_of_base_lift fixedIntegerBaseCanonical
    854041599922236190937524347070927377276592590715779683450880000 sigma
    fixedIntegerBaseCanonical_cast

end InternalCatalan

end

end

end OAI
