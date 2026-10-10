import OAI.Combinatorics.Crossing.PolynomialMinors
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {μ ν : Type*} [Fintype μ] [Fintype ν]

theorem exists_row_minor [DecidableEq ν] (A : Matrix μ ν ℝ) (hA : LinearIndependent ℝ A.col) :
    ∃ r : ν → μ, Function.Injective r ∧ (A.submatrix r id).det ≠ 0 := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ A.row
  let : Fintype ι := Fintype.ofInjective a ha
  have hcard : Fintype.card ι = Fintype.card ν := by
    rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_row,
      A.rank_eq_finrank_span_cols, finrank_span_eq_card hA]
  let e : ν ≃ ι := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hrows : LinearIndependent ℝ (A.submatrix (a ∘ e) id).row := hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

theorem exists_rank_minor (A : Matrix μ ν ℝ) :
    ∃ (r : Fin A.rank → μ) (c : Fin A.rank → ν),
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ A.col
  let : Fintype ι := Fintype.ofInjective a ha
  have hcard : Fintype.card ι = A.rank := by
    rw [← finrank_span_eq_card hli, hspan, A.rank_eq_finrank_span_cols]
  let e : Fin A.rank ≃ ι := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let c : Fin A.rank → ν := a ∘ e
  have hc : LinearIndependent ℝ (A.submatrix id c).col := hli.comp e e.injective
  obtain ⟨r, hr, hd⟩ := exists_row_minor (A.submatrix id c) hc
  refine ⟨r, c, hr, ha.comp e.injective, ?_⟩
  simpa [Matrix.submatrix_submatrix] using hd

theorem polynomial_rank_specialization (M : Matrix μ ν ℝ[X]) (nodes : Finset ℝ)
    (b : ℕ) (hb : ∀ t ∉ nodes, (M.map (Polynomial.eval t)).rank ≤ b) (t₀ : ℝ) :
    (M.map (Polynomial.eval t₀)).rank ≤ b := by
  classical
  let A := M.map (Polynomial.eval t₀)
  by_contra h
  have hlt : b < A.rank := Nat.lt_of_not_ge h
  obtain ⟨r, c, hr, hc, hd⟩ := exists_rank_minor A
  let P : ℝ[X] := (M.submatrix r c).det
  have evalP (t : ℝ) : P.eval t = ((M.map (Polynomial.eval t)).submatrix r c).det := by
    exact (evalRingHom t).map_det (M.submatrix r c)
  have hP : P ≠ 0 := by
    intro hzero
    apply hd
    change ((M.map (Polynomial.eval t₀)).submatrix r c).det = 0
    rw [← evalP, hzero, eval_zero]
  obtain ⟨t, ht⟩ := (nodes ∪ P.roots.toFinset).exists_notMem
  have htN : t ∉ nodes := fun htn => ht (Finset.mem_union_left _ htn)
  have htP : P.eval t ≠ 0 := by
    intro hz
    exact ht (Finset.mem_union_right _ (by simpa [mem_roots hP] using hz))
  have hm : (((M.map (Polynomial.eval t)).submatrix r c)).rank = A.rank := by
    simpa using Matrix.rank_of_det_ne_zero (show
      ((M.map (Polynomial.eval t)).submatrix r c).det ≠ 0 by rwa [← evalP])
  have hle := Matrix.rank_submatrix_le (M.map (Polynomial.eval t)) r c
  rw [hm] at hle
  exact (not_le_of_gt hlt) (hle.trans (hb t htN))

end Zarankiewicz

end

end OAI
