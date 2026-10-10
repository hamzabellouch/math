import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.ZeroAffineShell
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice

namespace OAI


noncomputable section

namespace Problem355.PrimePowerRowData

open Matrix PrimitiveNormal PairingDivisor

def integerLift {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  C.map (fun z => (z.val : ℤ))

@[simp] theorem integerLift_reduction {h : ℕ} [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    (integerLift C).map (Int.castRingHom (ZMod h)) = C := by
  ext i j
  simp [integerLift]

abbrev rowModule {h : ℕ} (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    Submodule ℤ (Fin 3 → ℤ) :=
  (RowLattice.integerRowLattice h C).toIntSubmodule

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

theorem integerLift_row_mem (hB : B.Prime) (i : Fin 3) :
    integerLift C i ∈ rowModule C := by
  let : NeZero B := ⟨hB.ne_zero⟩
  exact RowLattice.row_mem_integerRowLattice_of_reduction_eq (B ^ k)
    (integerLift C) C 1 (by simpa only [Matrix.one_mul] using integerLift_reduction C) i

theorem integerLift_diagonalization (d : PrimePowerData B k C) (hB : B.Prime) :
    (integerLift C).map (Int.castRingHom (ZMod (B ^ k))) =
      (d.left : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ d.b, (B : ZMod (B ^ k)) ^ d.e] *
          (d.right : Matrix _ _ _) := by
  let : NeZero B := ⟨hB.ne_zero⟩
  rw [integerLift_reduction]
  simpa only [Nat.cast_pow] using d.diagonalization

theorem rowModule_index (d : PrimePowerData B k C) (hB : B.Prime) :
    (rowModule C).toAddSubgroup.index = B ^ (d.b + d.e) := by
  change (RowLattice.integerRowLattice (B ^ k) C).index = _
  rw [d.row_lattice_index hB.ne_zero, pow_add]

theorem larger_divisor_nsmul_mem (d : PrimePowerData B k C) (v : Fin 3 → ℤ) :
    (B ^ d.e) • v ∈ rowModule C :=
  d.multiple_mem_row_lattice v

theorem larger_divisor_zsmul_mem (d : PrimePowerData B k C) (v : Fin 3 → ℤ) :
    ((B ^ d.e : ℕ) : ℤ) • v ∈ rowModule C := by
  simpa only [Nat.cast_smul_eq_nsmul] using larger_divisor_nsmul_mem d v

theorem larger_divisor_isUnit (d : PrimePowerData B k C) {q : ℕ}
    (hcop : (B ^ k).Coprime q) :
    IsUnit (((B ^ d.e : ℕ) : ℤ) : ZMod q) := by
  have he : (B ^ d.e).Coprime q :=
    hcop.of_dvd_left (Nat.pow_dvd_pow B d.e_le_k)
  simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ d.e) q).mpr he

theorem pairing_pos_and_dvd (d : PrimePowerData B k C) (hB : B.Prime)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    0 < pairingDivisor (rowModule C).toAddSubgroup x ∧
      pairingDivisor (rowModule C).toAddSubgroup x ∣ B ^ d.e := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  exact pairingDivisor_pos_and_dvd (rowModule C).toAddSubgroup x z hz
    (B ^ d.e) (pow_pos hB.pos _) (larger_divisor_nsmul_mem d)

theorem pairing_cube_le (d : PrimePowerData B k C) (hB : B.Prime)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    (pairingDivisor (rowModule C).toAddSubgroup x : ℝ) ^ 3 ≤
      ((B : ℝ) ^ (d.b + d.e)) * ((B : ℝ) ^ k) ^ 2 := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  have h := LatticeMoment.pairing_divisor_cube_div_index_le
    (rowModule C).toAddSubgroup x z B d.b d.e k hB.pos d.e_le_k hz
    (larger_divisor_nsmul_mem d)
  have hpos : 0 < (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by
    have : (0 : ℝ) < B := by exact_mod_cast hB.pos
    positivity
  have hd := (div_le_iff₀ hpos).mp h
  simpa only [pow_add, mul_comm] using hd

theorem plane_covolume (d : PrimePowerData B k C) (hB : B.Prime)
    (x : Fin 3 → ℤ) (hx : IsPrimitive x) :
    ZLattice.covolume (IntegralPlaneLattice.latticeIn x (rowModule C)) =
      ((B : ℝ) ^ (d.b + d.e)) * ‖toEuclidean x‖ /
        (pairingDivisor (rowModule C).toAddSubgroup x : ℝ) := by
  rw [ZeroAffineShell.canonical_pairing_covolume x hx (rowModule C)
    (B ^ d.e) (pow_pos hB.pos _) (larger_divisor_nsmul_mem d),
    rowModule_index d hB]
  push_cast
  rfl

theorem orbit_rows_mem (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ Section04Orbit.slOrbit C)
    (i : Fin 3) : A i ∈ rowModule C :=
  OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit (B ^ k) C A hA i

end Problem355.PrimePowerRowData

end

end OAI
