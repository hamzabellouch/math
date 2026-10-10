import OAI.Geometry.HeilbronnTriangle.PrimePowerRowData
import OAI.Geometry.HeilbronnTriangle.ZeroDeterminantCount

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open ZeroDeterminantCount

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

def toZeroRowData (d : PrimePowerData B k C) (hB : B.Prime) : RowData where
  B := B
  b := d.b
  e := d.e
  k := k
  prime := hB
  e_le_k := d.e_le_k
  L := PrimePowerRowData.rowModule C
  C := PrimePowerRowData.integerLift C
  P := d.left
  Q := d.right
  diagonal := PrimePowerRowData.integerLift_diagonalization d hB
  contains := PrimePowerRowData.larger_divisor_nsmul_mem d
  rows := PrimePowerRowData.integerLift_row_mem hB
  index_eq := PrimePowerRowData.rowModule_index d hB

@[simp] theorem toZeroRowData_L (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).L =
      (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule := rfl

@[simp] theorem toZeroRowData_h (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).h = (B : ℝ) ^ k := rfl

@[simp] theorem toZeroRowData_I (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).I = B ^ (d.b + d.e) := rfl

@[simp] theorem toZeroRowData_E (d : PrimePowerData B k C) (hB : B.Prime) :
    (d.toZeroRowData hB).E = B ^ d.e := rfl

theorem toZeroRowData_index_real (d : PrimePowerData B k C) (hB : B.Prime) :
    ((d.toZeroRowData hB).I : ℝ) = (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by
  simp only [toZeroRowData_I, pow_add, Nat.cast_mul, Nat.cast_pow]

theorem orbit_rows_mem_toZeroRowData (d : PrimePowerData B k C) (hB : B.Prime)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ Section04Orbit.slOrbit C)
    (i : Fin 3) : A i ∈ (d.toZeroRowData hB).L :=
  PrimePowerRowData.orbit_rows_mem A hA i

theorem toZeroRowData_E_isUnit (d : PrimePowerData B k C) (hB : B.Prime)
    {q : ℕ} (hcop : (B ^ k).Coprime q) :
    IsUnit ((d.toZeroRowData hB).E : ZMod q) := by
  simpa only [toZeroRowData_E, Int.cast_natCast] using
    PrimePowerRowData.larger_divisor_isUnit d hcop

end Problem355.PrimePowerData

end

end OAI
