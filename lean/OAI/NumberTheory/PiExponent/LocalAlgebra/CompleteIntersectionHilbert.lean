import OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def degreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i), (Polynomial.X : Polynomial ℤ) ^ j

theorem degreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (degreePolynomial D m).eval 1 = ∏ i ∈ Finset.range m, (D i : ℤ) := by
  simp [degreePolynomial, Polynomial.eval_prod, Polynomial.eval_finsetSum]

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_polynomial
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) := by
  rw [regular_sequence_series_geometric hσ rs degrees hhom hreg hlen]
  change _ = (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range rs.length, ∑ j ∈ Finset.range (degreeAt degrees i),
      (Polynomial.X : Polynomial ℤ) ^ j)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_section_dimension_coeff
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (n : ℕ) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℤ) =
      (degreePolynomial (degreeAt degrees) rs.length).coeff n := by
  have h := congrArg (PowerSeries.coeff n)
    (regular_sequence_series_polynomial hσ rs degrees hhom hreg hlen)
  simpa only [coeff_sectionHilbertSeries, Polynomial.coeff_coe] using h

theorem regular_sequence_section_dimension_eq_zero
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (n : ℕ)
    (hn : n ∉ (degreePolynomial (degreeAt degrees) rs.length).support) :
    Module.finrank k (quotientSection (Ideal.ofList rs) n) = 0 := by
  have h := regular_sequence_section_dimension_coeff hσ rs degrees hhom hreg hlen n
  have hz : (degreePolynomial (degreeAt degrees) rs.length).coeff n = 0 := by
    simpa only [Polynomial.mem_support_iff, not_not] using hn
  rw [hz] at h
  exact_mod_cast h

theorem regular_sequence_section_dimension_sum
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) :
    (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
      Module.finrank k (quotientSection (Ideal.ofList rs) n)) =
      ∏ i ∈ Finset.range rs.length, degreeAt degrees i := by
  have h :
      (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
        (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℤ)) =
        ∏ i ∈ Finset.range rs.length, (degreeAt degrees i : ℤ) := by
    calc
      _ = ∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
          (degreePolynomial (degreeAt degrees) rs.length).coeff n := by
        apply Finset.sum_congr rfl
        intro n _
        exact regular_sequence_section_dimension_coeff hσ rs degrees hhom hreg hlen n
      _ = (degreePolynomial (degreeAt degrees) rs.length).eval 1 := by
        simp [Polynomial.eval_eq_sum, Polynomial.sum]
      _ = _ := degreePolynomial_eval_one _ _
  exact_mod_cast h

theorem regular_sequence_section_dimension_sum_le
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (D : ℕ)
    (hD : ∀ i, degrees i ≤ D) :
    (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
      Module.finrank k (quotientSection (Ideal.ofList rs) n)) ≤ D ^ rs.length := by
  rw [regular_sequence_section_dimension_sum hσ rs degrees hhom hreg hlen]
  calc
    _ ≤ ∏ _i ∈ Finset.range rs.length, D := by
      apply Finset.prod_le_prod
      intro i hi
      simpa only [degreeAt, dite_eq_left (Finset.mem_range.mp hi)] using
        hD ⟨i, Finset.mem_range.mp hi⟩
    _ = _ := by simp

end PiExponentJets.W64

end OAI
