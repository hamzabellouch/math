import OAI.Geometry.HeilbronnTriangle.RowLatticeMatrices
import OAI.Geometry.HeilbronnTriangle.ZeroAffineShell

namespace OAI


noncomputable section

namespace Problem355.MatrixAffineShell

open scoped BigOperators Matrix
open Matrix RowLatticeMatrices PrimitiveNormal

theorem weighted_matrix_shell_le
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : IntMatrix) (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W x A ≤ W₀)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  let T := fun x => rowFamily x L (F x) (hF x)
  let V := fun x u => W x ((rowsEquiv x L).symm u).val
  have h := ZeroAffineShell.weighted_lattice_shell_le S L C B R b e k
    hB hRpos hR hek P Q hC hnorm hprimitive hcontain hrows T V N W₀
    hN hW₀
    (fun x hx u hu => hW x hx _ ((mem_rowFamily x L (F x) (hF x) u).mp hu))
    (fun x hx => rowFamily_norm_le_four_mul x L (F x) (hF x) hN (hcoord x hx))
    (fun x hx => rowFamily_independent_of_projections x L (F x) (hF x) (hproj x hx))
    hindex
  have heq : (∑ x ∈ S, ∑ u ∈ T x, V x u) = ∑ x ∈ S, ∑ A ∈ F x, W x A := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_rowFamily x L (F x) (hF x) (W x)
  rw [heq] at h
  exact h

theorem weighted_matrix_shell_le_of_short_exclusion
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : IntMatrix) (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W x A ≤ W₀)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hexclude : ∀ x ∈ S, ∀ A ∈ F x, 0 < W x A →
      ((B : ℝ) ^ k) ^ 2 < ‖toEuclidean x‖)
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  let T := fun x => rowFamily x L (F x) (hF x)
  let V := fun x u => W x ((rowsEquiv x L).symm u).val
  have h := ZeroAffineShell.weighted_lattice_shell_le_of_short_exclusion S L C B R b e k
    hB hRpos hek P Q hC hnorm hprimitive hcontain hrows T V N W₀
    hN hW₀
    (fun x hx u hu => hW x hx _ ((mem_rowFamily x L (F x) (hF x) u).mp hu))
    (fun x hx => rowFamily_norm_le_four_mul x L (F x) (hF x) hN (hcoord x hx))
    (fun x hx => rowFamily_independent_of_projections x L (F x) (hF x) (hproj x hx))
    (fun x hx u hu hpos => hexclude x hx _
      ((mem_rowFamily x L (F x) (hF x) u).mp hu) hpos)
    hindex
  have heq : (∑ x ∈ S, ∑ u ∈ T x, V x u) = ∑ x ∈ S, ∑ A ∈ F x, W x A := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_rowFamily x L (F x) (hF x) (W x)
  rw [heq] at h
  exact h

end Problem355.MatrixAffineShell

end

end OAI
