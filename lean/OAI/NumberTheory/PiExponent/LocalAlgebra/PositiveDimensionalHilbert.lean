import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.HilbertPoly
import OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_general
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    sectionHilbertSeries (Ideal.ofList rs) =
      (∏ i ∈ Finset.range rs.length, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  have h := regular_prefix_series rs degrees hhom hreg rs.length le_rfl
  simp only [List.take_length] at h
  rwa [sectionHilbertSeries_bot hσ] at h

theorem degreePolynomial_coe (D : ℕ → ℕ) (m : ℕ) :
    ((degreePolynomial D m) : PowerSeries ℤ) =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
      (Polynomial.X : Polynomial ℤ) ^ j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ - rs.length)).val := by
  rw [regular_sequence_series_general hσ rs degrees hhom hreg]
  have hn : Fintype.card σ = rs.length + (Fintype.card σ - rs.length) :=
    (Nat.add_sub_of_le hlen).symm
  have hi := congrArg (PowerSeries.invOneSubPow ℤ) hn
  rw [PowerSeries.invOneSubPow_add] at hi
  rw [hi, Units.val_mul, ← mul_assoc,
    degree_factors_mul_invOneSubPow, ← degreePolynomial_coe]

noncomputable def rationalSectionHilbertSeries (I : Ideal (MvPolynomial σ k)) :
    PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) (sectionHilbertSeries I)

omit [Fintype σ] in
@[simp] theorem coeff_rationalSectionHilbertSeries
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (rationalSectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
  simp [rationalSectionHilbertSeries, PowerSeries.coeff_map]

noncomputable def rationalDegreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℚ :=
  (degreePolynomial D m).map (Int.castRingHom ℚ)

theorem rationalDegreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (rationalDegreePolynomial D m).eval 1 =
      (∏ i ∈ Finset.range m, D i : ℕ) := by
  rw [rationalDegreePolynomial, Polynomial.eval_one_map, degreePolynomial_eval_one]
  simp

theorem map_int_invOneSubPow (r : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOneSubPow ℤ r).val =
      (PowerSeries.invOneSubPow ℚ r).val := by
  cases r with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp [PowerSeries.coeff_map]

theorem rational_regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    rationalSectionHilbertSeries (Ideal.ofList rs) =
      ((rationalDegreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ - rs.length)).val := by
  rw [rationalSectionHilbertSeries,
    regular_sequence_series_residual hσ rs degrees hhom hreg hlen,
    map_mul, map_int_invOneSubPow]
  rw [← Polynomial.polynomial_map_coe]
  rfl

noncomputable def regularSequenceHilbertPolynomial
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ) : Polynomial ℚ :=
  Polynomial.hilbertPoly (rationalDegreePolynomial (degreeAt degrees) rs.length)
    (Fintype.card σ - rs.length)

theorem regularSequenceHilbertPolynomial_eventually_exact
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) (n : ℕ)
    (hn : (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree < n) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) =
      (regularSequenceHilbertPolynomial rs degrees).eval (n : ℚ) := by
  rw [← coeff_rationalSectionHilbertSeries,
    rational_regular_sequence_series_residual hσ rs degrees hhom hreg hlen]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem hilbertPolynomial_top_coefficient (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).coeff (r-1) =
      p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ,
    Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_preHilbertPoly_self]
  rw [← Finset.sum_mul]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum]

theorem hilbertPolynomial_natDegree_le (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).natDegree ≤ r-1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ s i).le

theorem hilbertPolynomial_degree_and_leading
    (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) (hp : p.eval 1 ≠ 0) :
    (Polynomial.hilbertPoly p r).natDegree = r-1 ∧
      (Polynomial.hilbertPoly p r).leadingCoeff = p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  have hf : (((r-1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r-1)
  have hc : (Polynomial.hilbertPoly p r).coeff (r-1) ≠ 0 := by
    rw [hilbertPolynomial_top_coefficient p r hr]
    exact mul_ne_zero hp (inv_ne_zero hf)
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hilbertPolynomial_natDegree_le p r hr) hc
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hilbertPolynomial_top_coefficient p r hr]

noncomputable def hilbertMultiplicity (p : Polynomial ℚ) (ringDimension : ℕ) : ℚ :=
  p.coeff (ringDimension-1) * ((ringDimension-1).factorial : ℚ)

theorem regularSequenceHilbertPolynomial_multiplicity
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hlen : rs.length < Fintype.card σ) :
    hilbertMultiplicity (regularSequenceHilbertPolynomial rs degrees)
        (Fintype.card σ - rs.length) =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  have hr : 0 < Fintype.card σ - rs.length := Nat.sub_pos_of_lt hlen
  have hf : (((Fintype.card σ - rs.length - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card σ - rs.length - 1)
  rw [hilbertMultiplicity, regularSequenceHilbertPolynomial,
    hilbertPolynomial_top_coefficient _ _ hr, mul_assoc, inv_mul_cancel₀ hf,
    mul_one, rationalDegreePolynomial_eval_one]

theorem regular_sequence_has_hilbert_polynomial_with_degree_product
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N < n →
        (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) = p.eval (n : ℚ)) ∧
      hilbertMultiplicity p (Fintype.card σ - rs.length) =
        (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  refine ⟨regularSequenceHilbertPolynomial rs degrees, ?_,
    regularSequenceHilbertPolynomial_multiplicity rs degrees hlen⟩
  refine ⟨(rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree, ?_⟩
  intro n hn
  exact regularSequenceHilbertPolynomial_eventually_exact hσ rs degrees hhom hreg hlen.le n hn

end PiExponentJets.W64

end OAI
