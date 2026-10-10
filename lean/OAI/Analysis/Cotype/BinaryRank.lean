import OAI.Analysis.Cotype.Rectangles
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def binaryMatrix (P : (ι × κ) → Bool) : Matrix ι κ (ZMod 2) :=
  fun i j => if P (i,j) then 1 else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem cross_eq_of_rank_le_one (A : Matrix ι κ (ZMod 2)) (hA : A.rank ≤ 1)
    (i i₀ : ι) (j j₀ : κ) : A i j * A i₀ j₀ = A i j₀ * A i₀ j := by
  let B : Matrix (Fin 2) (Fin 2) (ZMod 2) := A.submatrix ![i, i₀] ![j, j₀]
  have hr : B.rank ≤ 1 := (Matrix.rank_submatrix_le A _ _).trans hA
  by_contra h
  have hd : B.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    exact sub_ne_zero.mpr h
  have hh := Matrix.rank_of_det_ne_zero hd
  have : B.rank = 2 := by simpa using hh
  omega

theorem binary_rank_le_one_rectangle {P : (ι × κ) → Bool}
    (hP : (binaryMatrix P).rank ≤ 1) (hne : ∃ ij, P ij = true) :
    ∃ (s : Finset ι) (t : Finset κ), s.Nonempty ∧ t.Nonempty ∧ rectangle s t = P := by
  obtain ⟨⟨i₀,j₀⟩, h₀⟩ := hne
  let s := Finset.univ.filter (fun i => P (i,j₀) = true)
  let t := Finset.univ.filter (fun j => P (i₀,j) = true)
  refine ⟨s, t, ⟨i₀, by simp [s, h₀]⟩, ⟨j₀, by simp [t, h₀]⟩, ?_⟩
  funext ij
  obtain ⟨i,j⟩ := ij
  have hc := cross_eq_of_rank_le_one (binaryMatrix P) hP i i₀ j j₀
  simp only [binaryMatrix, h₀, ite_true, mul_one] at hc
  simp only [rectangle, s, t, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hp : P (i,j) <;> cases hi : P (i,j₀) <;> cases hj : P (i₀,j) <;>
    simp_all

omit [Fintype ι] in
theorem binary_rank_rectangle_le_one (s : Finset ι) (t : Finset κ) :
    (binaryMatrix (rectangle s t)).rank ≤ 1 := by
  have he : binaryMatrix (rectangle s t) = Matrix.vecMulVec
      (fun i => if i ∈ s then (1 : ZMod 2) else 0)
      (fun j => if j ∈ t then (1 : ZMod 2) else 0) := by
    ext i j
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ t <;>
      simp [binaryMatrix, rectangle, Matrix.vecMulVec, hi, hj]
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

theorem paritySign_rectangle (s : Finset ι) (t : Finset κ) :
    paritySign (rectangle s t) = (-1 : ℝ) ^ (s.card * t.card) := by
  rw [paritySign_eq]
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  rw [he, Finset.card_product]

theorem odd_rank_one_support {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f)
    {P : (ι × κ) → Bool} (hcoef : fourier f P ≠ 0)
    (hP : (binaryMatrix P).rank ≤ 1) :
    ∃ (s : Finset ι) (t : Finset κ),
      Odd s.card ∧ Odd t.card ∧ rectangle s t = P := by
  have hpar : paritySign P ≠ 1 := fun hp => hcoef (odd_even_coefficient_zero hf hp)
  have hne : ∃ ij, P ij = true := by
    by_contra h
    have hz (ij) : P ij = false := by
      cases hp : P ij <;> simp_all
    exact hpar (by simp [paritySign, hz])
  obtain ⟨s, t, _, _, he⟩ := binary_rank_le_one_rectangle hP hne
  have ho : Odd (s.card * t.card) := by
    by_contra h
    have heven := Nat.not_odd_iff_even.mp h
    apply hpar
    rw [← he, paritySign_rectangle]
    exact heven.neg_one_pow
  exact ⟨s, t, (Nat.odd_mul.mp ho).1, (Nat.odd_mul.mp ho).2, he⟩

end Cotype

end

end OAI
