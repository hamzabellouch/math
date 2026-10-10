import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.ZeroAffineShell

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open PairingDivisor PrimitiveNormal

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

theorem row_pairing_pos (d : PrimePowerData B k C) (hB : 0 < B)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    0 < pairingDivisor (RowLattice.integerRowLattice (B ^ k) C) x := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  exact (pairingDivisor_pos_and_dvd _ x z hz (B ^ d.e)
    (pow_pos hB _) d.multiple_mem_row_lattice).1

theorem row_pairing_cube_le (d : PrimePowerData B k C) (hB : 0 < B)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    (pairingDivisor (RowLattice.integerRowLattice (B ^ k) C) x : ℝ) ^ 3 ≤
      (B : ℝ) ^ (d.b + d.e) * ((B : ℝ) ^ k) ^ 2 := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have h := LatticeMoment.pairing_divisor_cube_div_index_le
    (RowLattice.integerRowLattice (B ^ k) C) x z B d.b d.e k hB d.e_le_k hz
    d.multiple_mem_row_lattice
  have hi : 0 < (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by positivity
  have hm := (div_le_iff₀ hi).mp h
  simpa only [pow_add, mul_comm] using hm

theorem row_plane_covolume (d : PrimePowerData B k C) (hB : 0 < B)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    ZLattice.covolume (IntegralPlaneLattice.latticeIn x
      (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule) =
      (B : ℝ) ^ (d.b + d.e) * ‖toEuclidean x‖ /
        (pairingDivisor (RowLattice.integerRowLattice (B ^ k) C) x : ℝ) := by
  have hc := ZeroAffineShell.canonical_pairing_covolume x hx
    (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
    (B ^ d.e) (pow_pos hB _) d.multiple_mem_row_lattice
  change ZLattice.covolume (IntegralPlaneLattice.latticeIn x
    (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule) =
      ((RowLattice.integerRowLattice (B ^ k) C).index : ℝ) * ‖toEuclidean x‖ /
        (pairingDivisor (RowLattice.integerRowLattice (B ^ k) C) x : ℝ) at hc
  rw [d.row_lattice_index (Nat.ne_of_gt hB)] at hc
  simpa only [Nat.cast_mul, Nat.cast_pow, pow_add] using hc

end Problem355.PrimePowerData

end

end OAI
