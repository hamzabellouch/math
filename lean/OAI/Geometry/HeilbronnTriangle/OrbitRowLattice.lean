import OAI.Geometry.HeilbronnTriangle.OrbitEstimate
import OAI.Geometry.HeilbronnTriangle.RowLattice

namespace OAI


namespace Problem355.OrbitRowLattice

open Matrix

variable {R : Type*} [CommRing R]

theorem rowImage_mul_left_unit
    (P : Matrix.GeneralLinearGroup (Fin 3) R) (C : Matrix (Fin 3) (Fin 3) R) :
    RowLattice.rowImage ((P : Matrix _ _ _) * C) = RowLattice.rowImage C := by
  ext y
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v ᵥ* (P : Matrix _ _ _), ?_⟩
    change v ᵥ* (P.val * C) = y at hv
    change (v ᵥ* P.val) ᵥ* C = y
    rw [Matrix.vecMul_vecMul]
    exact hv
  · rintro ⟨v, hv⟩
    refine ⟨v ᵥ* ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix _ _ _), ?_⟩
    change (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = y
    calc
      (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = v ᵥ* C := by
        rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      _ = y := hv

theorem rowImage_eq_of_mem_slOrbit
    {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ Section04Orbit.slOrbit C) :
    RowLattice.rowImage A = RowLattice.rowImage C := by
  obtain ⟨g, rfl⟩ := hA
  exact rowImage_mul_left_unit (Matrix.SpecialLinearGroup.toGL g) C

theorem row_mem_rowImage (C : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    C i ∈ RowLattice.rowImage C := by
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp [Matrix.single_vecMul]

theorem row_mem_integerRowLattice_of_reduction_mem_slOrbit
    (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C) (i : Fin 3) :
    A i ∈ RowLattice.integerRowLattice h C := by
  change (fun j => (A i j : ZMod h)) ∈ RowLattice.rowImage C
  rw [← rowImage_eq_of_mem_slOrbit hA]
  exact row_mem_rowImage (A.map (Int.castRingHom (ZMod h))) i

theorem det_eq_of_mem_slOrbit
    {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ Section04Orbit.slOrbit C) :
    A.det = C.det := by
  obtain ⟨g, rfl⟩ := hA
  rw [Matrix.det_mul, g.property, one_mul]

theorem det_cast_eq_of_reduction_mem_slOrbit
    (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C) :
    (A.det : ZMod h) = C.det := by
  have hd := det_eq_of_mem_slOrbit hA
  change (Int.castRingHom (ZMod h)) A.det = C.det
  rw [RingHom.map_det]
  exact hd

theorem small_representative_unique {a b h T : ℤ}
    (hmod : a ≡ b [ZMOD h]) (ha : |a| ≤ T) (hb : |b| ≤ T) (hT : 2 * T < h) :
    a = b := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hab : |b - a| < h := abs_lt.mpr ⟨by omega, by omega⟩
  have hd : h ∣ |b - a| := (dvd_abs h (b - a)).mpr (Int.modEq_iff_dvd.mp hmod)
  have hz : |b - a| = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) hab hd
  exact (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm

theorem small_determinants_unique
    (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C)
    (hB : B.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C)
    {T : ℤ} (ha : |A.det| ≤ T) (hb : |B.det| ≤ T) (hT : 2 * T < h) :
    A.det = B.det := by
  apply small_representative_unique (h := (h : ℤ)) (T := T) _ ha hb hT
  apply (ZMod.intCast_eq_intCast_iff _ _ h).mp
  exact (det_cast_eq_of_reduction_mem_slOrbit h C A hA).trans
    (det_cast_eq_of_reduction_mem_slOrbit h C B hB).symm

end Problem355.OrbitRowLattice

end OAI
