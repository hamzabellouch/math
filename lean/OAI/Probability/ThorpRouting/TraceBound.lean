import OAI.Probability.ThorpRouting.TraceDecay

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma trace_re_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    (LinearMap.trace ℂ V A.toLinearMap).re ≤ (Module.finrank ℂ V : ℝ) * ‖A‖ := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  calc
    _ ≤ ∑ j : Fin (Module.finrank ℂ V), ‖A‖ := by
      apply Finset.sum_le_sum
      intro j _
      change (inner ℂ (B j) (A (B j))).re ≤ ‖A‖
      apply (Complex.re_le_norm _).trans
      apply (norm_inner_le_norm _ _).trans
      simpa only [B.norm_eq_one, one_mul, mul_one] using A.le_opNorm (B j)
    _ = _ := by simp

lemma trace_power_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) (u : ℕ) (hu : 0 < u) :
    (LinearMap.trace ℂ V (A^u).toLinearMap).re ≤
      (Module.finrank ℂ V : ℝ) * ‖A‖^u :=
  (trace_re_le_dimension_norm (A^u)).trans
    (mul_le_mul_of_nonneg_left (norm_pow_le' A hu) (Nat.cast_nonneg _))

lemma full_row_dimension (μ : YoungDiagram) (hμ : μ.rowLen 0 = μ.card) :
    Module.finrank ℂ (hilbertSpace μ) = 1 := by
  rw [finrank_hilbertSpace]
  have hle := Submodule.finrank_le (space μ)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have hc : Fintype.card (Tabloid μ) ≤ 1 := by
    let := tabloid_subsingleton_of_full_row μ hμ
    exact Fintype.card_le_one_iff.mpr (fun _ _ => Subsingleton.elim _ _)
  exact Nat.le_antisymm (hle.trans hc) (dimension_pos μ)

lemma full_row_unique (n : ℕ) (μ ν : Shapes n)
    (hμ : μ.1.card - μ.1.rowLen 0 = 0) (hν : ν.1.card - ν.1.rowLen 0 = 0) : μ = ν := by
  have hcells (γ : Shapes n) (hγ : γ.1.card - γ.1.rowLen 0 = 0) :
      γ.1.cells = {0} ×ˢ Finset.range n := by
    have hrow : γ.1.rowLen 0 = γ.1.card := by have := rowLen_zero_le_card γ.1; omega
    have he : γ.1.row 0 = γ.1.cells := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset _ _) (by rw [←γ.1.rowLen_eq_card]; exact hrow.ge)
    rw [←he, YoungDiagram.row_eq_prod, hrow, γ.2]
  apply Subtype.ext
  apply YoungDiagram.ext
  exact (hcells μ hμ).trans (hcells ν hν).symm

lemma full_row_count (n : ℕ) :
    (∑ μ : Shapes n, if μ.1.card - μ.1.rowLen 0 = 0 then (1 : ℝ) else 0) ≤ 1 := by
  have hc : (Finset.univ.filter (fun μ : Shapes n => μ.1.card - μ.1.rowLen 0 = 0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro μ hμ ν hν
    exact full_row_unique n μ ν (Finset.mem_filter.mp hμ).2 (Finset.mem_filter.mp hν).2
  rw [Finset.sum_boole]
  exact_mod_cast hc

lemma full_row_trace (d u : ℕ) (μ : Shapes (2^d)) (hμ : μ.1.card - μ.1.rowLen 0 = 0) :
    (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
      absoluteTrace (V := hilbertSpace μ.1) (Q d μ) (2 * (u : ℝ)) = 1 := by
  have hrow : μ.1.rowLen 0 = μ.1.card := by have := rowLen_zero_le_card μ.1; omega
  have hK : K d μ.1 (cardLabels d μ) = 1 :=
    sampleOperator_trivial (V := hilbertSpace μ.1) _
      (relabelled_full_row μ.1 hrow (cardLabels d μ)) _
  rw [absoluteTrace_even, Q_square, hK, one_pow, full_row_dimension μ.1 hrow]
  simp [full_row_dimension μ.1 hrow]

lemma regularTrace_le (d u : ℕ) (hu : 0 < u) :
    regularTrace d (2 * (u : ℝ)) ≤ 1 + tailBound d u := by
  have hterm (μ : Shapes (2^d)) :
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
        absoluteTrace (V := hilbertSpace μ.1) (Q d μ) (2 * (u : ℝ)) ≤
      (if μ.1.card - μ.1.rowLen 0 = 0 then 1 else 0) +
        (if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
          (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^u) := by
    by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
    · simp only [hz, ite_true, add_zero, full_row_trace d u μ hz, le_refl]
    · simp only [hz, ite_false, zero_add]
      rw [absoluteTrace_even, Q_square, pow_two, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (trace_power_le_dimension_norm (V := hilbertSpace μ.1) (K d μ.1 (cardLabels d μ)) u hu) (Nat.cast_nonneg _)
  calc
    regularTrace d (2 * (u : ℝ)) ≤
        (∑ μ : Shapes (2^d), if μ.1.card - μ.1.rowLen 0 = 0 then (1 : ℝ) else 0) +
          tailBound d u := by
      rw [tailBound, ←Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun μ _ => hterm μ)
    _ ≤ _ := add_le_add (full_row_count _) le_rfl

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
