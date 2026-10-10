import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators

namespace MatrixMultiplication.OrbitCounting

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

def orbitSet (x : X) : Finset X := Finset.univ.image fun g : G => g • x

@[simp] theorem smul_mem_orbitSet (x : X) (g : G) : g • x ∈ orbitSet (G := G) x := by
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

theorem card_fiber_eq (x y : X) (hy : y ∈ orbitSet (G := G) x) :
    Fintype.card {g : G // g • x = y} = Fintype.card {g : G // g • x = x} := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hy
  let e : {g : G // g • x = y} ≃ {g : G // g • x = x} :=
    { toFun := fun g => ⟨r⁻¹ * g.1, by
        rw [mul_smul, g.2, ← hr, inv_smul_smul]⟩
      invFun := fun g => ⟨r * g.1, by
        rw [mul_smul, g.2, hr]⟩
      left_inv := by intro g; apply Subtype.ext; simp
      right_inv := by intro g; apply Subtype.ext; simp }
  exact Fintype.card_congr e

theorem card_group (x : X) :
    Fintype.card G = (orbitSet (G := G) x).card *
      Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquiv (fun g : G => g • x)
    (fun y => y ∈ orbitSet (G := G) x) (smul_mem_orbitSet x)
  calc
    Fintype.card G = Fintype.card (Σ y : {y // y ∈ orbitSet (G := G) x},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ orbitSet (G := G) x},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 y.2
    _ = _ := by simp

theorem bad_shift_count (x : X) (bad : X → Prop) [DecidablePred bad] :
    (Finset.univ.filter fun g : G => bad (g • x)).card =
      ((orbitSet (G := G) x).filter bad).card *
        Fintype.card {g : G // g • x = x} := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (fun g : G => g • x)
    (p := fun g => bad (g • x))
    (q := fun y => y ∈ (orbitSet (G := G) x).filter bad)
    (fun g => by simp)
  calc
    (Finset.univ.filter fun g : G => bad (g • x)).card =
        Fintype.card {g : G // bad (g • x)} := (Fintype.card_subtype _).symm
    _ = Fintype.card (Σ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        {g : G // g • x = y.1}) := (Fintype.card_congr e).symm
    _ = ∑ y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = y.1} := Fintype.card_sigma
    _ = ∑ _y : {y // y ∈ (orbitSet (G := G) x).filter bad},
        Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_fiber_eq x y.1 (Finset.mem_filter.mp y.2).1
    _ = _ := by simp

theorem bad_shift_bound (x : X) (bad : X → Prop) [DecidablePred bad] (N C : ℕ)
    (h : N * ((orbitSet (G := G) x).filter bad).card ≤ C * (orbitSet (G := G) x).card) :
    N * (Finset.univ.filter fun g : G => bad (g • x)).card ≤ C * Fintype.card G := by
  rw [bad_shift_count, card_group (G := G) x]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
    (Fintype.card {g : G // g • x = x}) h

theorem bad_shift_fraction (x : X) (bad : X → Prop) [DecidablePred bad] :
    ((Finset.univ.filter fun g : G => bad (g • x)).card : ℝ) / Fintype.card G =
      (((orbitSet (G := G) x).filter bad).card : ℝ) / (orbitSet (G := G) x).card := by
  have hsNat : 0 < Fintype.card {g : G // g • x = x} :=
    Fintype.card_pos_iff.mpr ⟨⟨1, one_smul G x⟩⟩
  have hs : (Fintype.card {g : G // g • x = x} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsNat)
  rw [bad_shift_count, card_group (G := G) x]
  simp only [Nat.cast_mul]
  exact mul_div_mul_right _ _ hs

end MatrixMultiplication.OrbitCounting

end OAI
