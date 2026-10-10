import OAI.Analysis.KadisonKastler.FiniteTraceMatrix
import OAI.Analysis.KadisonKastler.TracialMatrixBracketAverage
import OAI.Analysis.KadisonKastler.FiniteInnerTransport

namespace OAI

/-! # Constructed finite-factor projection averages -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
/-- The ambient operator order agrees with the algebraic projection order. -/
theorem ambient_projection_le {p q : AlgebraProjection M} (hpq : p ≤ q) :
    p.val.val ≤ q.val.val := by
  apply ((p.property.map M.toStarSubalgebra.subtype).le_iff_mul_eq_right
    (q.property.map M.toStarSubalgebra.subtype)).mpr
  exact congrArg Subtype.val hpq

/-- Consecutive equal-trace matrix cuts give an average within one matrix slot. -/
theorem exists_average_of_consecutive_matrix_cuts (τ : TracialRepresentation M)
    {n m : ℕ} (hn : 0 < n) (hm : m < n)
    (E : MatrixUnitSystem (Fin n) (Algebra M))
    (ht : ∀ i, τ.trace (E.entry i i) = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (p : AlgebraProjection M)
    (hlo : matrixDiagonalCut E (Finset.univ.filter (fun i => i.val < m)) ≤ p)
    (hhi : p ≤ matrixDiagonalCut E
      (insert ⟨m, hm⟩ (Finset.univ.filter (fun i => i.val < m)))) :
    ∃ A : FiniteInnerAverage M,
      ‖A.apply p.val.val - (((m : ℝ) / n : ℝ) : ℂ) • (1 : H →L[ℂ] H)‖ ≤ (n : ℝ)⁻¹ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let F := E.map M.toStarSubalgebra.subtype
  have hF : F.algebra ≤ M.toStarSubalgebra :=
    (F.algebra_le_iff _).mpr (fun i j => (E.entry i j).property)
  let s := Finset.univ.filter (fun i : Fin n => i.val < m)
  let j : Fin n := ⟨m, hm⟩
  let q := matrixDiagonalCut E s
  let r := matrixDiagonalCut E (insert j s)
  have hj : j ∉ s := by simp [s, j]
  have hmemb (s' : Finset (Fin n)) : (matrixDiagonalCut E s').val.val ∈ F.algebra := by
    change (M.toStarSubalgebra.subtype (∑ i ∈ s', E.entry i i)) ∈ F.algebra
    rw [map_sum]
    exact F.algebra.sum_mem (fun i _ => F.entry_mem i i)
  have hqt : τ.trace q.val = (((m : ℝ) / n : ℝ) : ℂ) :=
    initial_matrix_cut_trace τ hm.le E ht
  have hrt : τ.trace r.val = ((((m : ℝ) + 1) / n : ℝ) : ℂ) := by
    rw [matrixDiagonalCut_trace τ E _ ht, Finset.card_insert_of_notMem hj]
    have hc : s.card = m := by
      exact (Fin.card_filter_val_lt).trans (min_eq_right hm.le)
    rw [hc]
    push_cast
    rfl
  obtain ⟨A, hA⟩ := exists_scalar_average_of_tracial_matrix_bracket τ F hF p q r
    (hmemb s) (hmemb (insert j s)) ((m : ℝ) / n) (((m : ℝ) + 1) / n)
    (by apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n))
    hqt hrt (ambient_projection_le hlo) (ambient_projection_le hhi)
  refine ⟨A, ?_⟩
  have he : ((m : ℝ) + 1) / n - (m : ℝ) / n = (n : ℝ)⁻¹ := by ring
  rwa [he] at hA

/-- Every projection of trace below one has scalar finite averages with
arbitrarily small error, obtained by rational cuts and inner transport. -/
theorem exists_projection_scalar_average_of_trace_lt_one (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : AlgebraProjection M) (hp : (τ.trace p.val).re < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply p.val.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let n := k + 1
  obtain ⟨E, m, hm, r, u, ht, hlo, hhi, hu⟩ :=
    exists_rational_matrix_bracket τ hfactor hdiff p hp n (Nat.succ_pos k)
  obtain ⟨A, hA⟩ := exists_average_of_consecutive_matrix_cuts τ (Nat.succ_pos k)
    hm E ht r hlo hhi
  let f := Unitary.conjStarAlgAut ℂ (Algebra M) u
  have hup : f r.val = p.val := hu
  refine ⟨A.map f, (((m : ℝ) / n : ℝ) : ℂ), ?_⟩
  rw [← FiniteInnerAverage.algebraApply_val, ← hup,
    A.norm_map_inner_sub_scalar u r.val]
  rw [FiniteInnerAverage.algebraApply_val]
  exact hA.trans_lt (by simpa only [one_div, Nat.cast_succ] using hk)

end

end KadisonKastler

end OAI
