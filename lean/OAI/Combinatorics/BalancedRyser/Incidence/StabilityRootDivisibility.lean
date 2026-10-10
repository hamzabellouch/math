import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic

namespace OAI

namespace Balanced.StabilityPolynomial

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

theorem splits_dvd_vanishing_mul_derivative {R : F[X]} (hR : R.Splits) :
    R ∣ (X ^ Fintype.card F - X) * derivative R := by
  induction hR using Submonoid.closure_induction with
  | mem P hP =>
    rcases hP with (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · simp
    · have hroot : (X - C (-c) : F[X]) ∣ X ^ Fintype.card F - X := by
        apply dvd_iff_isRoot.mpr
        simp [IsRoot, FiniteField.pow_card]
      simpa using hroot
  | one => simp
  | mul P Q _ _ hP hQ =>
    have hsum := dvd_add (mul_dvd_mul hP (dvd_refl Q))
      (mul_dvd_mul (dvd_refl P) hQ)
    convert hsum using 1
    rw [derivative_mul]
    ring

theorem split_mul_dvd_vanishing_derivative_mul
    {R : F[X]} (hR : R.Splits) (A : F[X]) :
    R * A ∣ (X ^ Fintype.card F - X) * derivative (R * A) * A := by
  obtain ⟨T, hT⟩ := splits_dvd_vanishing_mul_derivative hR
  refine ⟨T * A + (X ^ Fintype.card F - X) * derivative A, ?_⟩
  rw [derivative_mul]
  calc
    (X ^ Fintype.card F - X) * (derivative R * A + R * derivative A) * A =
        ((X ^ Fintype.card F - X) * derivative R) * A ^ 2 +
          (R * A) * ((X ^ Fintype.card F - X) * derivative A) := by ring
    _ = R * A * (T * A + (X ^ Fintype.card F - X) * derivative A) := by
      rw [hT]
      ring

theorem redei_wronskian_divisibility
    {R A f g : F[X]} (hR : R.Splits)
    (hidentity : R * A = X ^ Fintype.card F * f + g) :
    R * A ∣ (X * f + g) * (derivative f * g - derivative g * f) * A := by
  let H := R * A
  let V : F[X] := X ^ Fintype.card F - X
  have hH : H = X ^ Fintype.card F * f + g := hidentity
  have hdH : derivative H = X ^ Fintype.card F * derivative f + derivative g := by
    rw [hH, derivative_add, derivative_mul, derivative_X_pow]
    simp
  have hfirst : X * f + g = H - V * f := by
    rw [hH]
    dsimp [V]
    ring
  have hsecond : derivative f * g - derivative g * f =
      derivative f * H - f * derivative H := by
    rw [hdH, hH]
    ring
  have hdiv : H ∣ V * derivative H * A :=
    split_mul_dvd_vanishing_derivative_mul hR A
  have hdiv' := dvd_mul_of_dvd_left hdiv (f ^ 2)
  have hmain : H ∣ H * ((H * derivative f - f * derivative H -
      V * f * derivative f) * A) := dvd_mul_right H _
  have hsum := dvd_add hmain hdiv'
  change H ∣ _
  rw [hfirst, hsecond]
  convert hsum using 1
  ring

omit [Fintype F] in

theorem exists_split_auxiliary_of_dvd
    {R A H : F[X]} (hR : R.Splits) (hR0 : R ≠ 0) (hA0 : A ≠ 0)
    (hdiv : H ∣ R * A) :
    ∃ S B : F[X], S.Splits ∧ B.natDegree ≤ A.natDegree ∧ H = S * B := by
  obtain ⟨S, B, hS, hB, hH⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  exact ⟨S, B, hR.of_dvd hR0 hS, natDegree_le_of_dvd hB hA0, hH⟩

theorem redei_factor_wronskian_divisibility
    {R A H f g : F[X]} (hR : R.Splits) (hR0 : R ≠ 0)
    (hdiv : H ∣ R * A)
    (hidentity : H = X ^ Fintype.card F * f + g) :
    H ∣ (X * f + g) * (derivative f * g - derivative g * f) * A := by
  obtain ⟨S, B, hS, hB, hH⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  have hsplit := hR.of_dvd hR0 hS
  have hSB : S * B = X ^ Fintype.card F * f + g := hH.symm.trans hidentity
  have hbase := redei_wronskian_divisibility hsplit hSB
  obtain ⟨C, hC⟩ := hB
  rw [hH, hC]
  simpa only [mul_assoc] using dvd_mul_of_dvd_left hbase C

theorem linear_product_wronskian_divisibility
    {ι : Type*} (s : Finset ι) (a : ι → F) {A f g : F[X]}
    (hidentity : (∏ i ∈ s, (X + C (a i))) * A =
      X ^ Fintype.card F * f + g) :
    (∏ i ∈ s, (X + C (a i))) * A ∣
      (X * f + g) * (derivative f * g - derivative g * f) * A := by
  apply redei_wronskian_divisibility (hidentity := hidentity)
  exact Splits.prod fun i _ => Splits.X_add_C (a i)

end Balanced.StabilityPolynomial

end OAI
