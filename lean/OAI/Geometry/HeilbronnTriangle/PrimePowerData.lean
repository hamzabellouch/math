import OAI.Geometry.HeilbronnTriangle.OrbitEstimate
import OAI.Geometry.HeilbronnTriangle.RowLattice
import OAI.Geometry.HeilbronnTriangle.MinorInvariant
import OAI.Geometry.HeilbronnTriangle.TwoByTwoSmith
import OAI.Geometry.HeilbronnTriangle.PivotAssembly

namespace OAI


namespace Problem355

structure PrimePowerData (p k : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) where
  b : ℕ
  e : ℕ
  b_le_e : b ≤ e
  e_le_k : e ≤ k
  left : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
  right : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))
  diagonalization : C = (left : Matrix _ _ _) *
    Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
      ((p ^ e : ℕ) : ZMod (p ^ k))] * (right : Matrix _ _ _)

namespace PrimePowerData

variable {p k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))}

theorem nonempty_of_unit (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
    Nonempty (PrimePowerData p k C) := by
  let rel : ZMod (p ^ k) → ZMod (p ^ k) → Prop := fun x y =>
    ∃ b e : ℕ, b ≤ e ∧ e ≤ k ∧
      x = (p : ZMod (p ^ k)) ^ b ∧ y = (p : ZMod (p ^ k)) ^ e
  have hdiag : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)),
      ∃ P Q : Matrix.GeneralLinearGroup (Fin 2) (ZMod (p ^ k)),
      ∃ x y : ZMod (p ^ k), rel x y ∧
        A = (P : Matrix _ _ _) * Matrix.diagonal ![x, y] * (Q : Matrix _ _ _) := by
    intro A
    obtain ⟨b, e, hbe, hek, P, Q, hA⟩ := TwoByTwoSmith.exists_prime_power_diagonal hp k A
    exact ⟨P, Q, _, _, ⟨b, e, hbe, hek, rfl, rfl⟩, hA⟩
  obtain ⟨P, Q, x, y, hrel, hC⟩ :=
    PivotAssembly.exists_factorization_of_two_by_two_units rel hdiag C hunit
  obtain ⟨b, e, hbe, hek, hx, hy⟩ := hrel
  refine ⟨⟨b, e, hbe, hek, P, Q, ?_⟩⟩
  rw [hx, hy] at hC
  simpa only [Nat.cast_pow] using hC

noncomputable def ofUnit (hp : p.Prime) (hunit : IsUnit (C 0 0)) :
    PrimePowerData p k C :=
  Classical.choice (nonempty_of_unit hp hunit)

lemma b_le_k (d : PrimePowerData p k C) : d.b ≤ k :=
  d.b_le_e.trans d.e_le_k

theorem row_lattice_index (d : PrimePowerData p k C) (hp : p ≠ 0) :
    (RowLattice.integerRowLattice (p ^ k) C).index = p ^ d.b * p ^ d.e := by
  let : NeZero p := ⟨hp⟩
  apply RowLattice.integerRowLattice_index_prime_power p k d.b d.e
    d.b_le_k d.e_le_k C d.left d.right
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem multiple_mem_row_lattice (d : PrimePowerData p k C) (v : Fin 3 → ℤ) :
    (p ^ d.e) • v ∈ RowLattice.integerRowLattice (p ^ k) C := by
  apply RowLattice.nsmul_mem_integerRowLattice_prime_power p k d.b d.e
    d.b_le_e C d.left d.right _ v
  simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization

theorem orbit_lower_bound (d : PrimePowerData p k C) (hp : p.Prime) (hk : 0 < k) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (Section04Orbit.slOrbit C) : ℝ) :=
  Section04Orbit.slOrbit_lower_bound hp hk d.b_le_k d.e_le_k
    C d.left d.right d.diagonalization

theorem minors_vanish_iff (d : PrimePowerData p k C) (hp : p.Prime)
    {j : ℕ} (hj : j ≤ k) :
    UnitPivot.MinorsVanish
      (C.map (ZMod.castHom (Nat.pow_dvd_pow p hj) (ZMod (p ^ j)))) ↔ j ≤ d.b :=
  UnitPivot.minorsVanish_reduce_prime_power_iff hp d.b_le_e hj
    d.left d.right C d.diagonalization

theorem b_unique (d d' : PrimePowerData p k C) (hp : p.Prime) : d.b = d'.b := by
  apply Nat.le_antisymm
  · exact (d'.minors_vanish_iff hp d.b_le_k).mp
      ((d.minors_vanish_iff hp d.b_le_k).mpr le_rfl)
  · exact (d.minors_vanish_iff hp d'.b_le_k).mp
      ((d'.minors_vanish_iff hp d'.b_le_k).mpr le_rfl)

theorem e_unique (d d' : PrimePowerData p k C) (hp : p.Prime) : d.e = d'.e := by
  have hindex := (d.row_lattice_index hp.ne_zero).symm.trans
    (d'.row_lattice_index hp.ne_zero)
  rw [d.b_unique d' hp] at hindex
  exact Nat.pow_right_injective hp.two_le
    (Nat.mul_left_cancel (pow_pos hp.pos _) hindex)

end PrimePowerData

end Problem355

end OAI
