import OAI.Analysis.KadisonKastler.MatrixProjectionInterpolation
import OAI.Analysis.FactorGeneration.UniformPartitions
import Mathlib.Data.Fintype.Fin

namespace OAI

/-! # Uniform trace matrices and rational projection brackets -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A diffuse finite factor contains a full matrix algebra of every positive
size, with the prescribed normalized diagonal trace. -/
theorem exists_uniform_trace_matrix (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (n : ℕ) (hn : 0 < n) :
    ∃ E : MatrixUnitSystem (Fin n) (Algebra M),
      ∀ i, τ.trace (E.entry i i) = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨Q, hsize, ht⟩ := exists_uniform_trace_partition τ hdiff n
    (identityProjection M) (n : ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) (by
      change τ.trace 1 = (n : ℂ) * (((n : ℝ)⁻¹ : ℝ) : ℂ)
      simp [τ.trace_one, hn.ne'])
  subst n
  obtain ⟨E, hdiag, _⟩ := exists_matrixAlgebra_for_unit_partition τ hfactor Q hn
    (fun i j => (ht i).trans (ht j).symm)
  exact ⟨E, fun i => by rw [hdiag]; exact ht i⟩

/-- The initial diagonal cut has exactly the expected rational trace. -/
theorem initial_matrix_cut_trace (τ : TracialRepresentation M)
    {n m : ℕ} (hm : m ≤ n) (E : MatrixUnitSystem (Fin n) (Algebra M))
    (ht : ∀ i, τ.trace (E.entry i i) = (((n : ℝ)⁻¹ : ℝ) : ℂ)) :
    τ.trace (matrixDiagonalCut E (Finset.univ.filter (fun i => i.val < m))).val =
      (((m : ℝ) / n : ℝ) : ℂ) := by
  rw [matrixDiagonalCut_trace τ E _ ht, Fin.card_filter_val_lt, min_eq_right hm]
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_natCast]

/-- A nonendpoint trace is bracketed by consecutive rational grid values. -/
theorem exists_rational_trace_bracket (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, m < n ∧ (m : ℝ) / n ≤ t ∧ t ≤ ((m : ℝ) + 1) / n := by
  let m := ⌊t * n⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmlo : (m : ℝ) ≤ t * n := Nat.floor_le (mul_nonneg ht hnR.le)
  have hmhi : t * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmn : m < n := by
    have h : (m : ℝ) < n := hmlo.trans_lt (by nlinarith)
    exact_mod_cast h
  exact ⟨m, hmn, (div_le_iff₀ hnR).mpr hmlo, (le_div_iff₀ hnR).mpr hmhi.le⟩

/-- After an inner conjugacy, every projection with trace below one lies
between two consecutive cuts of an arbitrarily chosen matrix size. -/
theorem exists_rational_matrix_bracket (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : AlgebraProjection M) (hp1 : (τ.trace p.val).re < 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ (E : MatrixUnitSystem (Fin n) (Algebra M)) (m : ℕ) (hm : m < n)
      (r : AlgebraProjection M) (u : unitary (Algebra M)),
      (∀ i, τ.trace (E.entry i i) = (((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      matrixDiagonalCut E (Finset.univ.filter (fun i => i.val < m)) ≤ r ∧
      r ≤ matrixDiagonalCut E (insert ⟨m, hm⟩ (Finset.univ.filter (fun i => i.val < m))) ∧
      (u : Algebra M) * r.val * star (u : Algebra M) = p.val := by
  obtain ⟨E, ht⟩ := exists_uniform_trace_matrix τ hfactor hdiff n hn
  obtain ⟨m, hm, hlo, hhi⟩ := exists_rational_trace_bracket (τ.trace p.val).re
    (by rw [projection_trace_sq τ p.val p.property]; positivity) hp1 n hn
  let s := Finset.univ.filter (fun i : Fin n => i.val < m)
  let j : Fin n := ⟨m, hm⟩
  have hj : j ∉ s := by simp [s, j]
  have hst := initial_matrix_cut_trace τ hm.le E ht
  have hsreal : (τ.trace (matrixDiagonalCut E s).val).re = (m : ℝ) / n :=
    congrArg Complex.re hst
  have hjreal : (τ.trace (E.entry j j)).re = (n : ℝ)⁻¹ := congrArg Complex.re (ht j)
  obtain ⟨r, u, hqr, hrt, hu⟩ := exists_projection_between_matrix_cuts τ hfactor hdiff
    E p s j hj (by rw [hsreal]; exact hlo) (by
      rw [hsreal, hjreal]
      simpa only [add_div, one_div] using hhi)
  exact ⟨E, m, hm, r, u, ht, hqr, hrt, hu⟩

end

end KadisonKastler

end OAI
