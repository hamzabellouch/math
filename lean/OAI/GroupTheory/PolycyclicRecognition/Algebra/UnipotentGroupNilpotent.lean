import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentProducts
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Nilpotence from a faithful upper-unipotent representation

The entry filtration records the diagonal on which a matrix can first be
nonzero. Commutators advance this filtration. The finite matrix size then
bounds the lower central series of the represented group.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {n : ℕ} {R : Type*} [Ring R]

/-- Vanishing on all diagonals strictly below the `k`-th upper diagonal. -/
def MatrixDepth (k : ℕ) (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + k → X i j = 0

namespace MatrixDepth

theorem zero (k : ℕ) : MatrixDepth k (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j _
  rfl

theorem mono {k l : ℕ} {X : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) (h : l ≤ k) : MatrixDepth l X := by
  intro i j hij
  exact hX i j (by omega)

theorem add {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) (hY : MatrixDepth k Y) : MatrixDepth k (X + Y) := by
  intro i j hij
  simp only [Matrix.add_apply, hX i j hij, hY i j hij, add_zero]

theorem neg {k : ℕ} {X : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) : MatrixDepth k (-X) := by
  intro i j hij
  simp only [Matrix.neg_apply, hX i j hij, neg_zero]

theorem sub {k : ℕ} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) (hY : MatrixDepth k Y) : MatrixDepth k (X - Y) := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem mul {k l : ℕ} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) (hY : MatrixDepth l Y) : MatrixDepth (k + l) (X * Y) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : (a : ℕ) < (i : ℕ) + k
  · rw [hX i a ha, zero_mul]
  · rw [hY a j (by omega), mul_zero]

theorem one : MatrixDepth 0 (1 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  have hne : i ≠ j := by intro h; subst j; omega
  simp [hne]

theorem eq_zero {k : ℕ} {X : Matrix (Fin n) (Fin n) R}
    (hX : MatrixDepth k X) (hk : n ≤ k) : X = 0 := by
  ext i j
  exact hX i j (by have := j.isLt; omega)

theorem of_strictUpper {X : Matrix (Fin n) (Fin n) R} (hX : StrictUpper X) :
    MatrixDepth 1 X := by
  intro i j hij
  exact hX i j (by change (j : ℕ) ≤ (i : ℕ); omega)

end MatrixDepth

variable {H : Type*} [Group H]

/-- A common finite upper-unipotent realization bounds the group lower
central series, without any finiteness assumption on the represented group. -/
theorem nilpotent_of_faithful_strictUpper_representation
    (ρ : H →* (Matrix (Fin n) (Fin n) R)ˣ) (hinj : Function.Injective ρ)
    (hu : ∀ h, StrictUpper ((ρ h : Matrix (Fin n) (Fin n) R) - 1)) :
    Group.IsNilpotent H := by
  let f : H →* Matrix (Fin n) (Fin n) R := (Units.coeHom _).comp ρ
  have h1 (g : H) : MatrixDepth 1 (f g - 1) := MatrixDepth.of_strictUpper (hu g)
  have h0 (g : H) : MatrixDepth 0 (f g) := by
    have h := (h1 g).mono (Nat.zero_le 1)
    simpa only [sub_add_cancel] using h.add MatrixDepth.one
  have hmul (g h : H) :
      f (g * h) - 1 = (f g - 1) + (f h - 1) + (f g - 1) * (f h - 1) := by
    rw [f.map_mul]
    noncomm_ring
  have hinv (g : H) : f g⁻¹ - 1 = -(f g⁻¹ * (f g - 1)) := by
    have he : f g⁻¹ * f g = 1 := by rw [← f.map_mul, inv_mul_cancel, f.map_one]
    rw [mul_sub, he]
    noncomm_ring
  let S (k : ℕ) : Subgroup H :=
    { carrier := {g | MatrixDepth k (f g - 1)}
      one_mem' := by
        change MatrixDepth k (f 1 - 1)
        rw [f.map_one, sub_self]
        exact MatrixDepth.zero k
      mul_mem' := by
        intro g h hg hh
        change MatrixDepth k (f (g * h) - 1)
        rw [hmul]
        exact (hg.add hh).add ((hg.mul hh).mono (by omega))
      inv_mem' := by
        intro g hg
        change MatrixDepth k (f g⁻¹ - 1)
        rw [hinv]
        simpa only [Nat.zero_add] using ((h0 g⁻¹).mul hg).neg }
  have hc (k : ℕ) (x y : H) (hx : x ∈ S k) : ⁅x, y⁆ ∈ S (k + 1) := by
    have hxy : MatrixDepth (k + 1)
        ((f x - 1) * (f y - 1) - (f y - 1) * (f x - 1)) :=
      (hx.mul (h1 y)).sub (by simpa only [Nat.add_comm] using (h1 y).mul hx)
    have hxi : f x * f x⁻¹ = 1 := by rw [← f.map_mul, mul_inv_cancel, f.map_one]
    have hyi : f y * f y⁻¹ = 1 := by rw [← f.map_mul, mul_inv_cancel, f.map_one]
    have he : f ⁅x, y⁆ - 1 =
        ((f x - 1) * (f y - 1) - (f y - 1) * (f x - 1)) * f x⁻¹ * f y⁻¹ := by
      simp only [commutatorElement_def, f.map_mul]
      calc
        _ = f x * f y * f x⁻¹ * f y⁻¹ - (f y * (f x * f x⁻¹)) * f y⁻¹ := by
          rw [hxi, mul_one, hyi]
        _ = _ := by noncomm_ring
    change MatrixDepth (k + 1) (f ⁅x, y⁆ - 1)
    rw [he]
    simpa only [Nat.add_zero] using (hxy.mul (h0 x⁻¹)).mul (h0 y⁻¹)
  have hs (k : ℕ) : (⊤ : Subgroup H).lowerCentralSeries k ≤ S (k + 1) := by
    induction k with
    | zero => exact fun g _ => h1 g
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_le.mpr (fun x hx y _ => hc (k + 1) x y (ih hx))
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨n, le_antisymm ?_ bot_le⟩
  intro g hg
  change g = 1
  apply hinj
  apply Units.ext
  change f g = f 1
  rw [f.map_one]
  exact sub_eq_zero.mp ((hs n hg).eq_zero (by omega))

end PolycyclicRecognition

end OAI
