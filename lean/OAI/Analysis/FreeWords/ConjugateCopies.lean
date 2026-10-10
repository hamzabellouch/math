import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

structure FreeMatrixCopies (τ : A →ₚ[ℂ] ℂ) (r d : ℕ) where
  inclusion : Fin r → Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A
  injective : ∀ j, Function.Injective (inclusion j)
  free : ScalarFree τ (fun j => (inclusion j).range)

namespace FreeMatrixCopies

variable (F : FreeMatrixCopies τ r d)

def diagonal (j : Fin r) (a : Fin d) : A := F.inclusion j (Matrix.single a a 1)

theorem diagonal_selfadjoint (j : Fin r) (a : Fin d) :
    star (F.diagonal j a) = F.diagonal j a := by
  rw [diagonal, ← map_star]
  congr 1
  change (Matrix.single a a (1:ℂ)).conjTranspose = _
  simp

theorem diagonal_mul (j : Fin r) (a b : Fin d) :
    F.diagonal j a * F.diagonal j b = if a=b then F.diagonal j a else 0 := by
  rw [diagonal, diagonal, ← map_mul]
  split_ifs with h
  · subst b
    simp
  · rw [Matrix.single_mul_single_of_ne 1 a a b h 1, map_zero]

theorem diagonal_sum (j : Fin r) : ∑ a, F.diagonal j a = 1 := by
  simp only [diagonal, ← map_sum, Matrix.sum_single_one, map_one]

theorem diagonal_trace_eq (hτ : ∀ x y : A, τ (x*y) = τ (y*x))
    (j : Fin r) (a b : Fin d) : τ (F.diagonal j a) = τ (F.diagonal j b) := by
  have h := hτ (F.inclusion j (Matrix.single a b 1)) (F.inclusion j (Matrix.single b a 1))
  simpa only [← map_mul, Matrix.single_mul_single_same, one_mul, diagonal] using h

theorem diagonal_trace (hτ : FaithfulTracial τ) (j : Fin r) (a : Fin d) :
    τ (F.diagonal j a) = (d:ℂ)⁻¹ := by
  have hs : (d:ℂ)*τ (F.diagonal j a) = 1 := by
    have h := congrArg τ (F.diagonal_sum j)
    rw [map_sum, hτ.1] at h
    simpa only [F.diagonal_trace_eq hτ.2.1 j _ a, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using h
  exact eq_inv_of_mul_eq_one_right hs

def toPartitions (hτ : FaithfulTracial τ) : FreePartitions τ r d where
  S j := (F.inclusion j).range
  e := F.diagonal
  mem _ a := ⟨Matrix.single a a 1, rfl⟩
  selfadjoint := F.diagonal_selfadjoint
  mul := F.diagonal_mul
  sum := F.diagonal_sum
  trace := F.diagonal_trace hτ
  free := F.free

end FreeMatrixCopies

end

end KKFreeWords
end

end OAI
