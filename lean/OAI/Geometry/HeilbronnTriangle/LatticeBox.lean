import Mathlib

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

def box (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N)

@[simp] theorem mem_box {d N : ℕ} {v : Fin d → ℤ} :
    v ∈ box d N ↔ ∀ i, |v i| ≤ (N : ℤ) := by
  simp [box, abs_le]

@[simp] theorem card_box (d N : ℕ) :
    (box d N).card = (2 * N + 1) ^ d := by
  simp [box, Int.card_Icc]
  congr 1
  omega

theorem card_le_of_coord_bound {d N : ℕ} (S : Finset (Fin d → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |v i| ≤ (N : ℤ)) :
    S.card ≤ (2 * N + 1) ^ d := by
  rw [← card_box]
  exact Finset.card_le_card (fun v hv => mem_box.mpr (hS v hv))

theorem int_abs_le_floor {a : ℤ} {R : ℝ} (h : |(a : ℝ)| ≤ R) :
    |a| ≤ (⌊R⌋₊ : ℤ) := by
  have hcast : (a.natAbs : ℝ) = |(a : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
  have hn : a.natAbs ≤ ⌊R⌋₊ := Nat.le_floor (hcast ▸ h)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hn

theorem card_le_of_real_coord_bound {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (Fin d → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ R) :
    (S.card : ℝ) ≤ (2 * R + 1) ^ d := by
  have hcount := card_le_of_coord_bound S
    (fun v hv i => int_abs_le_floor (hS v hv i))
  calc
    (S.card : ℝ) ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hcount
    _ = (2 * (⌊R⌋₊ : ℝ) + 1) ^ d := by norm_cast
    _ ≤ (2 * R + 1) ^ d := by
      gcongr
      exact Nat.floor_le hR

theorem card_le_twentyseven_mul_cube {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ R) :
    (S.card : ℝ) ≤ 27 * R ^ 3 := by
  calc
    (S.card : ℝ) ≤ (2 * R + 1) ^ 3 :=
      card_le_of_real_coord_bound (by linarith) S hS
    _ ≤ (3 * R) ^ 3 := by gcongr; linarith
    _ = 27 * R ^ 3 := by ring

theorem card_le_onehundredtwentyfive_mul_cube {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ 2 * R) :
    (S.card : ℝ) ≤ 125 * R ^ 3 := by
  calc
    (S.card : ℝ) ≤ (2 * (2 * R) + 1) ^ 3 :=
      card_le_of_real_coord_bound (by linarith) S hS
    _ ≤ (5 * R) ^ 3 := by gcongr; linarith
    _ = 125 * R ^ 3 := by ring

def realVector {d : ℕ} (v : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

theorem abs_coord_le_norm {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    |(v i : ℝ)| ≤ ‖realVector v‖ := by
  simpa [realVector, Real.norm_eq_abs] using PiLp.norm_apply_le (realVector v) i

theorem card_le_of_norm_bound {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ‖realVector v‖ ≤ R) :
    (S.card : ℝ) ≤ 27 * R ^ 3 :=
  card_le_twentyseven_mul_cube hR S
    (fun v hv i => (abs_coord_le_norm v i).trans (hS v hv))

theorem card_le_of_norm_bound_twice {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ‖realVector v‖ ≤ 2 * R) :
    (S.card : ℝ) ≤ 125 * R ^ 3 :=
  card_le_onehundredtwentyfive_mul_cube hR S
    (fun v hv i => (abs_coord_le_norm v i).trans (hS v hv))

end Problem355.LatticeBox

end

end OAI
