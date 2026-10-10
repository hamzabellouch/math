import OAI.LinearAlgebra.MatrixMultiplication.Recovery.ExactRecovery
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitCounting
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.OrbitRecovery

variable {G X Y Z : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def badShifts (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) : Finset G :=
  Finset.univ.filter fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z))

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem badShifts_card_le (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) :
    (badShifts (G := G) px py pz x y z).card ≤
      (Finset.univ.filter fun g : G => ¬px (g • x)).card +
      (Finset.univ.filter fun g : G => ¬py (g • y)).card +
      (Finset.univ.filter fun g : G => ¬pz (g • z)).card := by
  classical
  have heq : badShifts (G := G) px py pz x y z =
      (Finset.univ.filter fun g : G => ¬px (g • x)) ∪
      ((Finset.univ.filter fun g : G => ¬py (g • y)) ∪
        (Finset.univ.filter fun g : G => ¬pz (g • z))) := by
    ext g
    by_cases hx : px (g • x) <;> by_cases hy : py (g • y) <;>
      by_cases hz : pz (g • z) <;> simp [badShifts, hx, hy, hz]
  rw [heq]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_left (Finset.card_union_le _ _) _).trans (le_of_eq (Nat.add_assoc _ _ _).symm))

theorem badShifts_fraction_le_at (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (γ : ℝ) (x : X) (y : Y) (z : Z)
    (hx : (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    :
    ((badShifts (G := G) px py pz x y z).card : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hx' := hx
  have hy' := hy
  have hz' := hz
  rw [← OrbitCounting.bad_shift_fraction (G := G) x (fun v => ¬px v)] at hx'
  rw [← OrbitCounting.bad_shift_fraction (G := G) y (fun v => ¬py v)] at hy'
  rw [← OrbitCounting.bad_shift_fraction (G := G) z (fun v => ¬pz v)] at hz'
  have hxc := (div_le_iff₀ hg).mp hx'
  have hyc := (div_le_iff₀ hg).mp hy'
  have hzc := (div_le_iff₀ hg).mp hz'
  have hc : ((badShifts (G := G) px py pz x y z).card : ℝ) ≤
      ((Finset.univ.filter fun g : G => ¬px (g • x)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬py (g • y)).card : ℝ) +
      ((Finset.univ.filter fun g : G => ¬pz (g • z)).card : ℝ) := by
    exact_mod_cast badShifts_card_le (G := G) px py pz x y z
  apply (div_le_iff₀ hg).mpr
  linarith

theorem floor_loss_fraction (γ : ℝ) (hγ : 0 ≤ γ) :
    (Nat.floor (3 * γ * Fintype.card G) : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hg).mpr
  exact Nat.floor_le (by positivity)

theorem repair_from_orbit_loss
    {K : Type*} [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    (γ : ℝ)
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ γ)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ γ)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ γ)
    (L : ℕ) (hL : 0 < L)
    (hbudget : (@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card *
        Nat.floor (3 * γ * Fintype.card G) ^ L < Fintype.card G ^ L) :
    ∃ (a : X → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × X) → K)
      (b : Y → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Y) → K)
      (c : Z → ((Finset (Fin L) × Finset (Fin L) × Finset (Fin L)) × Z) → K),
      Tensor.restrict a b c (Tensor.directSum
        (fun _ : Finset (Fin L) × Finset (Fin L) × Finset (Fin L) =>
          ExactRecovery.delete Q px py pz)) = Q := by
  classical
  apply ExactRecovery.repair_of_counting (I := G) Q (ExactRecovery.delete Q px py pz)
    (fun g x => px (g • x)) (fun g y => py (g • y)) (fun g z => pz (g • z))
    (fun g x => g • x) (fun g y => g • y) (fun g z => g • z)
    (fun g x y z => by simp [ExactRecovery.delete, hpreserve])
    (Nat.floor (3 * γ * Fintype.card G)) L hL ?_ hbudget
  intro x y z hq
  have heq : (@Finset.filter G
      (fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z)))
      (Classical.decPred _) Finset.univ) = badShifts (G := G) px py pz x y z := by
    ext g
    simp only [badShifts, Finset.mem_filter]
  rw [heq]
  apply Nat.le_floor
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  exact (div_le_iff₀ hg).mp (badShifts_fraction_le_at (G := G) px py pz γ x y z
    (hx x ⟨y, z, hq⟩) (hy y ⟨x, z, hq⟩) (hz z ⟨x, y, hq⟩))

end MatrixMultiplication.OrbitRecovery

end OAI
