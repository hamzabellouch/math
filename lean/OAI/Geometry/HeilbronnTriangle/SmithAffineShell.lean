import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.MatrixAffineShell
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open scoped BigOperators Matrix
open Matrix PrimitiveNormal

theorem affine_shell_bound
    {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
    (d : PrimePowerData B k C) (hB : B.Prime)
    (S : Finset (Fin 3 → ℤ)) (R : ℕ) (hR : 0 < R)
    (hshell : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (F : (Fin 3 → ℤ) → Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hkernel : ∀ x ∈ S, ∀ A ∈ F x, A *ᵥ x = 0)
    (hrows : ∀ x ∈ S, ∀ A ∈ F x, ∀ i,
      A i ∈ RowLattice.integerRowLattice (B ^ k) C)
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W A ≤ W₀)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hexclude : ∀ x ∈ S, ∀ A ∈ F x, 0 < W A →
      ((B : ℝ) ^ k) ^ 2 < ‖toEuclidean x‖) :
    (∑ x ∈ S, ∑ A ∈ F x, W A) ≤
      1024 * W₀ * (144 * Real.pi) ^ 3 * N ^ 6 /
        ((B : ℝ) ^ (d.b + d.e)) ^ 2 := by
  classical
  let : NeZero (B ^ k) := ⟨pow_ne_zero _ hB.ne_zero⟩
  let C₀ : Matrix (Fin 3) (Fin 3) ℤ := C.map (fun a => (a.val : ℤ))
  have hred : C₀.map (Int.castRingHom (ZMod (B ^ k))) = C := by
    ext i j
    simp [C₀]
  let L := (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
  have hcontain : ∀ v : Fin 3 → ℤ, (B ^ d.e) • v ∈ L :=
    d.multiple_mem_row_lattice
  have hCrows : ∀ i, C₀ i ∈ L := by
    intro i
    change (fun j => (C₀ i j : ZMod (B ^ k))) ∈ RowLattice.rowImage C
    have hi := OrbitRowLattice.row_mem_rowImage C i
    simpa [C₀] using hi
  have hindex : L.toAddSubgroup.index = B ^ (d.b + d.e) := by
    change (RowLattice.integerRowLattice (B ^ k) C).index = _
    rw [d.row_lattice_index hB.ne_zero, pow_add]
  have hdiag : C₀.map (Int.castRingHom (ZMod (B ^ k))) =
      (d.left : Matrix _ _ _) *
        Matrix.diagonal ![1, (B : ZMod (B ^ k)) ^ d.b,
          (B : ZMod (B ^ k)) ^ d.e] * (d.right : Matrix _ _ _) := by
    rw [hred]
    simpa only [Nat.cast_pow] using d.diagonalization
  let F₀ := fun x => if x ∈ S then F x else ∅
  have hF₀ : ∀ x, ∀ A ∈ F₀ x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L := by
    intro x A hA
    by_cases hx : x ∈ S
    · have hA' : A ∈ F x := by simpa [F₀, hx] using hA
      exact ⟨hkernel x hx A hA', hrows x hx A hA'⟩
    · simp [F₀, hx] at hA
  have hmem : ∀ x ∈ S, ∀ A, A ∈ F₀ x ↔ A ∈ F x := by
    intro x hx A
    simp [F₀, hx]
  have h := MatrixAffineShell.weighted_matrix_shell_le_of_short_exclusion
    S L C₀ B R d.b d.e k hB hR d.e_le_k d.left d.right hdiag
    hshell hprimitive hcontain hCrows F₀ hF₀
    (fun _ A => W A) N W₀ hN hW₀
    (fun x hx A hA => hW x hx A ((hmem x hx A).mp hA))
    (fun x hx A hA => hcoord x hx A ((hmem x hx A).mp hA))
    (fun x hx A hA => hproj x hx A ((hmem x hx A).mp hA))
    (fun x hx A hA => hexclude x hx A ((hmem x hx A).mp hA)) hindex
  have heq : (∑ x ∈ S, ∑ A ∈ F₀ x, W A) = ∑ x ∈ S, ∑ A ∈ F x, W A := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [F₀, hx]
  rw [heq] at h
  convert h using 1; ring

end Problem355.PrimePowerData

end

end OAI
