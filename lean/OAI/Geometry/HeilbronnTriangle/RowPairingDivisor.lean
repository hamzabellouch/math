import OAI.Geometry.HeilbronnTriangle.PairingDivisor
import OAI.Geometry.HeilbronnTriangle.RowLattice

namespace OAI


namespace Problem355.RowPairingDivisor

open Matrix PairingDivisor RowLattice DiagonalStabilizer

theorem row_mem_rowImage {R : Type*} [CommRing R]
    (C : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) : C.row i ∈ rowImage C := by
  rw [rowImage_eq_rowSpan]
  exact Submodule.subset_span (Set.mem_range_self i)

theorem row_mem_integerRowLattice (h : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (i : Fin 3) :
    A.row i ∈ integerRowLattice h (A.map fun z : ℤ => (z : ZMod h)) := by
  change reduction h (A.row i) ∈ rowImage (A.map fun z : ℤ => (z : ZMod h))
  exact row_mem_rowImage _ i

noncomputable def matrixPairingDivisor (h : ℕ)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) : ℕ :=
  pairingDivisor (integerRowLattice h (A.map fun z : ℤ => (z : ZMod h))) x

theorem matrixPairingDivisor_dvd_mulVec (h : ℕ)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) (i : Fin 3) :
    (matrixPairingDivisor h A x : ℤ) ∣ (A.mulVec x) i := by
  change (pairingDivisor (integerRowLattice h (A.map fun z : ℤ => (z : ZMod h))) x : ℤ) ∣
    dotProduct (A.row i) x
  rw [dotProduct_comm]
  exact pairingDivisor_dvd_pairing _ x (A.row i) (row_mem_integerRowLattice h A i)

theorem matrixPairingDivisor_pos_and_dvd
    (B k b e : ℕ) (hB : 0 < B) (hbe : b ≤ e)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hA : (A.map fun z : ℤ => (z : ZMod (B ^ k))) =
      (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
        diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (x z : Fin 3 → ℤ) (hprimitive : dotProduct x z = 1) :
    0 < matrixPairingDivisor (B ^ k) A x ∧
      matrixPairingDivisor (B ^ k) A x ∣ B ^ e := by
  apply pairingDivisor_pos_and_dvd _ x z hprimitive (B ^ e) (pow_pos hB e)
  intro v
  exact nsmul_mem_integerRowLattice_prime_power B k b e hbe _ P Q hA v

end Problem355.RowPairingDivisor

end OAI
