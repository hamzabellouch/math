import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonalDifferential

namespace OAI

/-! # Component formula for the first-quadrant total differential -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped BigOperators
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module
open Finset.HasAntidiagonal

variable {R : Type} [CommRing R] (K : NatBicomplex R)

abbrev diagonalSucc₁ {n : ℕ} (p : ↥(antidiagonal n)) : ↥(antidiagonal (n + 1)) :=
  ⟨(p.1.1 + 1, p.1.2), mem_antidiagonal.mpr (by
    have := mem_antidiagonal.mp p.2; omega)⟩

abbrev diagonalSucc₂ {n : ℕ} (p : ↥(antidiagonal n)) : ↥(antidiagonal (n + 1)) :=
  ⟨(p.1.1, p.1.2 + 1), mem_antidiagonal.mpr (by
    have := mem_antidiagonal.mp p.2; omega)⟩

theorem bicomplex_horizontal_component (n : ℕ) (p : ↥(antidiagonal n))
    (x : bicomplexDiagonal K (n + 1)) :
    (∑ q : ↥(antidiagonal (n + 1)),
      bicomplexToDiagonal K n ((K.d₁ (ComplexShape.down ℕ) q.1.1 q.1.2 n).hom (x q))) p =
        ((K.d (p.1.1 + 1) p.1.1).f p.1.2).hom (x (diagonalSucc₁ p)) := by
  classical
  rw [Finset.sum_apply, Finset.sum_eq_single (diagonalSucc₁ p)]
  · rw [bicomplexToDiagonal_d₁_succ K n p.1.1 p.1.2 (mem_antidiagonal.mp p.2)]
    exact Pi.single_eq_same _ _
  · intro q _ hq
    rcases q with ⟨⟨i, j⟩, hqmem⟩
    cases i with
    | zero =>
      rw [bicomplexToDiagonal_d₁_zero]
      rfl
    | succ i =>
      have hij : i + j = n := by
        have := mem_antidiagonal.mp hqmem; omega
      rw [bicomplexToDiagonal_d₁_succ K n i j hij]
      apply Pi.single_eq_of_ne
      intro he
      apply hq
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      have h₁ := congrArg Prod.fst hv
      have h₂ := congrArg Prod.snd hv
      apply Prod.ext <;> dsimp [diagonalSucc₁] at * <;> omega
  · simp

theorem bicomplex_vertical_component (n : ℕ) (p : ↥(antidiagonal n))
    (x : bicomplexDiagonal K (n + 1)) :
    (∑ q : ↥(antidiagonal (n + 1)),
      bicomplexToDiagonal K n ((K.d₂ (ComplexShape.down ℕ) q.1.1 q.1.2 n).hom (x q))) p =
        (-1 : ℤˣ) ^ p.1.1 •
          ((K.X p.1.1).d (p.1.2 + 1) p.1.2).hom (x (diagonalSucc₂ p)) := by
  classical
  rw [Finset.sum_apply, Finset.sum_eq_single (diagonalSucc₂ p)]
  · rw [bicomplexToDiagonal_d₂_succ K n p.1.1 p.1.2 (mem_antidiagonal.mp p.2)]
    simp only [Pi.smul_apply, Pi.single_eq_same]
  · intro q _ hq
    rcases q with ⟨⟨i, j⟩, hqmem⟩
    cases j with
    | zero =>
      rw [bicomplexToDiagonal_d₂_zero]
      rfl
    | succ j =>
      have hij : i + j = n := by
        have := mem_antidiagonal.mp hqmem; omega
      rw [bicomplexToDiagonal_d₂_succ K n i j hij, Pi.smul_apply]
      have he : p ≠ ⟨(i, j), mem_antidiagonal.mpr hij⟩ := by
        intro he
        apply hq
        apply Subtype.ext
        have hv := congrArg Subtype.val he
        have h₁ := congrArg Prod.fst hv
        have h₂ := congrArg Prod.snd hv
        apply Prod.ext <;> dsimp [diagonalSucc₂] at * <;> omega
      rw [Pi.single_eq_of_ne he]
      simp only [Units.smul_def, zsmul_zero]
  · simp

theorem bicomplexDiagonalDifferential_apply (n : ℕ) (p : ↥(antidiagonal n))
    (x : bicomplexDiagonal K (n + 1)) :
    bicomplexDiagonalDifferential K n x p =
      ((K.d (p.1.1 + 1) p.1.1).f p.1.2).hom (x (diagonalSucc₁ p)) +
        (-1 : ℤˣ) ^ p.1.1 •
          ((K.X p.1.1).d (p.1.2 + 1) p.1.2).hom (x (diagonalSucc₂ p)) := by
  classical
  conv_lhs => rw [← LinearMap.sum_single_apply _ x]
  simp only [map_sum, bicomplexDiagonalDifferential_single, Finset.sum_add_distrib,
    Pi.add_apply]
  rw [bicomplex_horizontal_component, bicomplex_vertical_component]

end PolycyclicRecognition

end

end OAI
