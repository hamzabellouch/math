import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonalComponents

namespace OAI

/-! # Cycles and the leading component of a total boundary -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

variable {R : Type} [CommRing R] (K : NatBicomplex R)

def IsDiagonalCycle {n : ℕ} (x : bicomplexDiagonal K n) : Prop :=
  ∀ (i j : ℕ) (h : i + j + 1 = n),
    ((K.d (i + 1) i).f j).hom
        (x ⟨(i + 1, j), mem_antidiagonal.mpr (by omega)⟩) +
      (-1 : ℤˣ) ^ i • ((K.X i).d (j + 1) j).hom
        (x ⟨(i, j + 1), mem_antidiagonal.mpr (by omega)⟩) = 0

theorem diagonalBoundary_isCycle (n : ℕ) (x : bicomplexDiagonal K (n + 1)) :
    IsDiagonalCycle K (bicomplexDiagonalDifferential K n x) := by
  intro i j h
  subst n
  have he := congrFun (bicomplexDiagonalDifferential_squared K (i + j) x)
    ⟨(i, j), mem_antidiagonal.mpr rfl⟩
  rw [bicomplexDiagonalDifferential_apply] at he
  exact he

theorem IsDiagonalCycle.sub {n : ℕ} {x y : bicomplexDiagonal K n}
    (hx : IsDiagonalCycle K x) (hy : IsDiagonalCycle K y) :
    IsDiagonalCycle K (x - y) := by
  intro i j h
  have hx' := hx i j h
  have hy' := hy i j h
  simp only [Pi.sub_apply, map_sub, Units.smul_def, zsmul_sub]
  simp only [Units.smul_def] at hx' hy'
  have hz := congrArg₂ (fun a b : (K.X i).X j => a - b) hx' hy'
  simp only [sub_self] at hz
  convert hz using 1
  abel

theorem diagonalBoundary_single_above (n : ℕ) (p : ↥(antidiagonal n))
    (y : (K.X p.1.1).X (p.1.2 + 1)) (q : ↥(antidiagonal n)) (h : p.1.1 < q.1.1) :
    bicomplexDiagonalDifferential K n (Pi.single (diagonalSucc₂ p) y) q = 0 := by
  rw [bicomplexDiagonalDifferential_apply]
  have h₁ : diagonalSucc₁ q ≠ diagonalSucc₂ p := by
    intro he
    have := congrArg (fun r : ↥(antidiagonal (n + 1)) => r.1.1) he
    dsimp at this
    omega
  have h₂ : diagonalSucc₂ q ≠ diagonalSucc₂ p := by
    intro he
    have := congrArg (fun r : ↥(antidiagonal (n + 1)) => r.1.1) he
    dsimp at this
    omega
  rw [Pi.single_eq_of_ne h₁, Pi.single_eq_of_ne h₂, map_zero, map_zero, zero_add]
  simp only [Units.smul_def, zsmul_zero]

theorem diagonalBoundary_single_leading (n : ℕ) (p : ↥(antidiagonal n))
    (y : (K.X p.1.1).X (p.1.2 + 1)) :
    bicomplexDiagonalDifferential K n (Pi.single (diagonalSucc₂ p) y) p =
      (-1 : ℤˣ) ^ p.1.1 • ((K.X p.1.1).d (p.1.2 + 1) p.1.2).hom y := by
  rw [bicomplexDiagonalDifferential_apply]
  have h₁ : diagonalSucc₁ p ≠ diagonalSucc₂ p := by
    intro he
    have := congrArg (fun r : ↥(antidiagonal (n + 1)) => r.1.1) he
    dsimp at this
    omega
  rw [Pi.single_eq_of_ne h₁, Pi.single_eq_same, map_zero, zero_add]

theorem row_cycle_lift_of_exactAt (i j : ℕ) (hex : (K.X i).ExactAt j)
    (x : (K.X i).X j) (hx : ((K.X i).d j (j - 1)).hom x = 0) :
    ∃ y : (K.X i).X (j + 1), ((K.X i).d (j + 1) j).hom y = x := by
  have hp : (ComplexShape.down ℕ).prev j = j + 1 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  have hn : (ComplexShape.down ℕ).next j = j - 1 := by
    cases j with
    | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intros; simp [ComplexShape.down])
    | succ j => exact (ComplexShape.down ℕ).next_eq' rfl
  have he := ((K.X i).exactAt_iff' (j + 1) j (j - 1) hp hn).mp hex
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

theorem row_cycle_lift (hex : ∀ i j, (K.X i).ExactAt j) (i j : ℕ)
    (x : (K.X i).X j) (hx : ((K.X i).d j (j - 1)).hom x = 0) :
    ∃ y : (K.X i).X (j + 1), ((K.X i).d (j + 1) j).hom y = x :=
  row_cycle_lift_of_exactAt K i j (hex i j) x hx

end PolycyclicRecognition

end

end OAI
