import OAI.Geometry.HeilbronnTriangle.RowLattice
import OAI.Geometry.HeilbronnTriangle.IntegralAmbientLattice

namespace OAI


noncomputable section

namespace Problem355.RowLattice

open IntegralPlaneLattice

lemma modulus_smul_mem (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (v : Fin 3 → ℤ) : (h : ℤ) • v ∈ (integerRowLattice h C).toIntSubmodule := by
  change reduction h ((h : ℤ) • v) ∈ rowImage C
  have hr : reduction h ((h : ℤ) • v) = 0 := by
    ext i
    simp [reduction, zsmul_eq_mul]
  rw [hr]
  exact (rowImage C).zero_mem

abbrev realRowLattice (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :=
  realLattice (integerRowLattice h C).toIntSubmodule

instance realRowLattice_isZLattice (h : ℕ) [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) : IsZLattice ℝ (realRowLattice h C) := by
  exact realLattice_isZLattice _ (h : ℤ) (by exact_mod_cast NeZero.ne h)
    (modulus_smul_mem h C)

lemma realRowLattice_covolume (h : ℕ) [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    ZLattice.covolume (realRowLattice h C) = ((integerRowLattice h C).index : ℝ) := by
  exact realLattice_covolume _ (h : ℤ) (by exact_mod_cast NeZero.ne h)
    (modulus_smul_mem h C)

theorem realRowLattice_covolume_prime_power
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) :
    ZLattice.covolume (realRowLattice (B ^ k) C) = (B : ℝ) ^ b * (B : ℝ) ^ e := by
  rw [realRowLattice_covolume, integerRowLattice_index_prime_power B k b e hb he C P Q hC]
  push_cast
  rfl

end Problem355.RowLattice

end

end OAI
