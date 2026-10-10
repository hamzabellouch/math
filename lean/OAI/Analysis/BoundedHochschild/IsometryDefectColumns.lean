import OAI.Analysis.BoundedHochschild.PartialIsoProducts

namespace OAI

/-!
# Orthogonal columns from an isometry defect

A nonunitary isometry supplies countably many equivalent, orthogonal defect
projections. This is an algebraic ingredient of the properly infinite case.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

lemma isometry_pow_initial {v : M} (hv : star v * v = 1) (n : ℕ) :
    star (v ^ n) * v ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, star_mul]
      calc
        _ = star v * (star (v ^ n) * v ^ n) * v := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hv]

lemma isometry_pow_cancel {v : M} (hv : star v * v = 1) (n k : ℕ) :
    star (v ^ n) * v ^ (n + k) = v ^ k := by
  rw [pow_add, ← mul_assoc, isometry_pow_initial hv, one_mul]

def isometryDefect (v : M) : M := 1 - v * star v

lemma isometryDefect_projection {v : M} (hv : star v * v = 1) :
    IsStarProjection (isometryDefect v) := by
  apply IsStarProjection.one_sub
  refine ⟨?_, IsSelfAdjoint.mul_star_self v⟩
  calc
    (v * star v) * (v * star v) = v * (star v * v) * star v := by simp only [mul_assoc]
    _ = v * star v := by rw [hv, mul_one]

lemma isometryDefect_mul {v : M} (hv : star v * v = 1) :
    isometryDefect v * v = 0 := by
  rw [isometryDefect, sub_mul, one_mul, mul_assoc, hv, mul_one, sub_self]

lemma isometryDefect_mul_pow_succ {v : M} (hv : star v * v = 1) (n : ℕ) :
    isometryDefect v * v ^ (n + 1) = 0 := by
  rw [pow_succ', ← mul_assoc, isometryDefect_mul hv, zero_mul]

lemma isometry_column_initial {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (n : ℕ) :
    star (v ^ n * p) * (v ^ n * p) = p := by
  rw [star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ n) * v ^ n) * p := by simp only [mul_assoc]
    _ = p := by rw [isometry_pow_initial hv, mul_one, hp.isIdempotentElem.eq]

def isometryColumn (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) : PartialIso M :=
  ⟨v ^ n * p, by
    rw [mul_assoc, isometry_column_initial hv hp, mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] lemma isometryColumn_initial (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n).initial = p := isometry_column_initial hv hp n

@[simp] lemma isometryColumn_coe (v : M) (hv : star v * v = 1) (p : M)
    (hp : IsStarProjection p) (n : ℕ) :
    (isometryColumn v hv p hp n : M) = v ^ n * p := rfl

lemma isometryColumn_star_mul_of_lt {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i < j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hpk : p * v ^ (k + 1) = 0 := by
    rw [pow_succ', ← mul_assoc, hpv, zero_mul]
  simp only [isometryColumn_coe, star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ i) * v ^ (i + (k + 1))) * p := by
      simp only [mul_assoc, Nat.add_assoc]
    _ = 0 := by rw [isometry_pow_cancel hv, hpk, zero_mul]

lemma isometryColumn_star_mul_of_ne {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isometryColumn_star_mul_of_lt hv hp hpv h
  · simpa only [star_mul, star_star, star_zero] using
      congrArg star (isometryColumn_star_mul_of_lt hv hp hpv h)

lemma isometryColumn_final_orthogonal {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    (isometryColumn v hv p hp i).final * (isometryColumn v hv p hp j).final = 0 := by
  change (((isometryColumn v hv p hp i : M) * star (isometryColumn v hv p hp i : M)) *
    ((isometryColumn v hv p hp j : M) * star (isometryColumn v hv p hp j : M))) = 0
  rw [mul_assoc, ← mul_assoc (star (isometryColumn v hv p hp i : M)),
    isometryColumn_star_mul_of_ne hv hp hpv hij, zero_mul, mul_zero]

end BoundedHochschild.KadisonRingrose

end

end OAI
