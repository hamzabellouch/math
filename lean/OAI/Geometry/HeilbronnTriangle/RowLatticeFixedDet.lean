import OAI.Geometry.HeilbronnTriangle.FixedDetLattice
import OAI.Geometry.HeilbronnTriangle.AnisotropicEstimate
import OAI.Geometry.HeilbronnTriangle.RowLatticeVolume
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice

namespace OAI


noncomputable section

namespace Problem355.RowLatticeFixedDet

open IntegralPlaneLattice

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

theorem card_le_of_anisotropic
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (h : ℕ) [NeZero h] (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ RowLattice.integerRowLattice h C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ((RowLattice.integerRowLattice h C).index : ℝ) ^ 2 := by
  have hc := FixedDetLattice.integer_fixed_det_count a ha hanis
    (RowLattice.realRowLattice h C)
    (one_le_norm_of_mem_realLattice (RowLattice.integerRowLattice h C).toIntSubmodule)
    X hX S (fun A hA i => ⟨A i, hrows A hA i, rfl⟩) hnorm t ht hdet
  rw [RowLattice.realRowLattice_covolume] at hc
  exact hc

theorem orbit_card_le_of_anisotropic
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (h : ℕ) [NeZero h] (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S,
      A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ((RowLattice.integerRowLattice h C).index : ℝ) ^ 2 := by
  exact card_le_of_anisotropic a ha hanis h C X hX S
    (fun A hA i => OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit
      h C A (horbit A hA) i) hnorm t ht hdet

theorem prime_power_card_le_of_anisotropic
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ RowLattice.integerRowLattice (B ^ k) C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ((B : ℝ) ^ b * (B : ℝ) ^ e) ^ 2 := by
  have hc := card_le_of_anisotropic a ha hanis (B ^ k) C X hX S hrows hnorm t ht hdet
  rw [RowLattice.integerRowLattice_index_prime_power B k b e hb he C P Q hC] at hc
  simpa only [Nat.cast_mul, Nat.cast_pow] using hc

theorem card_le
    (h : ℕ) [NeZero h] (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ RowLattice.integerRowLattice h C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (FixedDetReduction.anisotropicConstant * 1000 ^ 6 * 144) *
      Real.log (2 * X) ^ 2 * X ^ 6 /
      ((RowLattice.integerRowLattice h C).index : ℝ) ^ 2 :=
  card_le_of_anisotropic _ FixedDetReduction.anisotropicConstant_pos.le
    FixedDetReduction.anisotropicEstimate h C X hX S hrows hnorm t ht hdet

theorem orbit_card_le
    (h : ℕ) [NeZero h] (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S,
      A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (FixedDetReduction.anisotropicConstant * 1000 ^ 6 * 144) *
      Real.log (2 * X) ^ 2 * X ^ 6 /
      ((RowLattice.integerRowLattice h C).index : ℝ) ^ 2 :=
  orbit_card_le_of_anisotropic _ FixedDetReduction.anisotropicConstant_pos.le
    FixedDetReduction.anisotropicEstimate h C X hX S horbit hnorm t ht hdet

theorem prime_power_card_le
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ RowLattice.integerRowLattice (B ^ k) C)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (FixedDetReduction.anisotropicConstant * 1000 ^ 6 * 144) *
      Real.log (2 * X) ^ 2 * X ^ 6 / ((B : ℝ) ^ b * (B : ℝ) ^ e) ^ 2 :=
  prime_power_card_le_of_anisotropic _ FixedDetReduction.anisotropicConstant_pos.le
    FixedDetReduction.anisotropicEstimate B k b e hb he C P Q hC X hX S
    hrows hnorm t ht hdet

end Problem355.RowLatticeFixedDet

end

end OAI
