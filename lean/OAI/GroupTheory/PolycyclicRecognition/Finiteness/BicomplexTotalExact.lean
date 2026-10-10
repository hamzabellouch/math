import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexFiniteElimination

namespace OAI

/-! # Exactness of first-quadrant total complexes with exact rows -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

variable {R : Type} [CommRing R] (K : NatBicomplex R)

theorem totalCycle_toDiagonal (n : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : ((K.total (ComplexShape.down ℕ)).d n (n - 1)).hom x = 0) :
    IsDiagonalCycle K (bicomplexToDiagonal K n x) := by
  intro i j h
  subst n
  have hz : bicomplexDiagonalDifferential K (i + j)
      (bicomplexToDiagonal K (i + j + 1) x) = 0 := by
    simp only [bicomplexDiagonalDifferential, LinearMap.comp_apply,
      bicomplexFromToDiagonal]
    have he : ((K.total (ComplexShape.down ℕ)).d (i + j + 1) (i + j)).hom x = 0 := by
      have hidx : i + j + 1 - 1 = i + j := by omega
      rw [hidx] at hx
      exact hx
    rw [he, map_zero]
  have hp := congrFun hz ⟨(i, j), mem_antidiagonal.mpr rfl⟩
  rw [bicomplexDiagonalDifferential_apply] at hp
  exact hp

theorem bicomplex_total_cycle_boundary_of_exact_diagonal (n : ℕ)
    (hex : ∀ i j, i + j = n → (K.X i).ExactAt j) (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : ((K.total (ComplexShape.down ℕ)).d n (n - 1)).hom x = 0) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n + 1),
      ((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom y = x := by
  obtain ⟨y, hy⟩ := diagonal_cycle_boundary_of_exact_diagonal K n hex (bicomplexToDiagonal K n x)
    (totalCycle_toDiagonal K n x hx)
  refine ⟨bicomplexFromDiagonal K (n + 1) y, ?_⟩
  apply (bicomplexDiagonalEquiv K n).injective
  exact hy

theorem bicomplex_total_exactAt_of_exact_diagonal (n : ℕ)
    (hex : ∀ i j, i + j = n → (K.X i).ExactAt j) :
    (K.total (ComplexShape.down ℕ)).ExactAt n := by
  have hp : (ComplexShape.down ℕ).prev n = n + 1 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  have hn : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n with
    | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intros; simp [ComplexShape.down])
    | succ n => exact (ComplexShape.down ℕ).next_eq' rfl
  apply ((K.total (ComplexShape.down ℕ)).exactAt_iff' (n + 1) n (n - 1) hp hn).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  exact bicomplex_total_cycle_boundary_of_exact_diagonal K n hex x hx

theorem bicomplex_total_cycle_boundary (hex : ∀ i j, (K.X i).ExactAt j)
    (n : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : ((K.total (ComplexShape.down ℕ)).d n (n - 1)).hom x = 0) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n + 1),
      ((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom y = x :=
  bicomplex_total_cycle_boundary_of_exact_diagonal K n (fun i j _ => hex i j) x hx

theorem bicomplex_total_exactAt (hex : ∀ i j, (K.X i).ExactAt j) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).ExactAt n :=
  bicomplex_total_exactAt_of_exact_diagonal K n (fun i j _ => hex i j)

theorem bicomplex_total_homology_isZero_of_diagonal (n : ℕ)
    (hz : ∀ i j, i + j = n → Limits.IsZero ((K.X i).homology j)) :
    Limits.IsZero ((K.total (ComplexShape.down ℕ)).homology n) :=
  (bicomplex_total_exactAt_of_exact_diagonal K n (fun i j hij =>
    ((K.X i).exactAt_iff_isZero_homology j).mpr (hz i j hij))).isZero_homology

theorem bicomplex_total_homology_isZero (hex : ∀ i j, (K.X i).ExactAt j) (n : ℕ) :
    Limits.IsZero ((K.total (ComplexShape.down ℕ)).homology n) :=
  (bicomplex_total_exactAt K hex n).isZero_homology

end PolycyclicRecognition

end

end OAI
