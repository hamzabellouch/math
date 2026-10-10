import Mathlib.Algebra.Ring.GeomSum
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes
import OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def degreeAt {m : ℕ} (degrees : Fin m → ℕ) (i : ℕ) : ℕ :=
  if hi : i < m then degrees ⟨i, hi⟩ else 0

theorem regular_prefix_series
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (n : ℕ) (hn : n ≤ rs.length) :
    sectionHilbertSeries (Ideal.ofList (rs.take n)) =
      (∏ i ∈ Finset.range n, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < rs.length := hn
    have hn' : n ≤ rs.length := Nat.le_of_lt hlt
    rw [PiExponentSiegel.W20.prefixIdeal_succ rs ⟨n, hlt⟩]
    simp only [Fin.getElem_fin]
    have hh : (rs[n]'hlt).IsHomogeneous (degrees ⟨n, hlt⟩) := by
      simpa only [Fin.getElem_fin] using hhom ⟨n, hlt⟩
    have hr : IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take n)) (rs[n]'hlt)) := by
      simpa only [Fin.getElem_fin] using
        PiExponentSiegel.W20.regular_next_mod_prefix rs hreg ⟨n, hlt⟩
    rw [sectionHilbertSeries_regular_step _
      (PiExponentSiegel.W20.prefixIdeal_homogeneous rs degrees hhom n)
      (rs[n]'hlt) hh hr]
    rw [ih hn', Finset.prod_range_succ]
    simp only [degreeAt, dite_eq_left hlt]
    ac_rfl

theorem degree_factors_mul_invOneSubPow (D : ℕ → ℕ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) *
      (PowerSeries.invOneSubPow ℤ m).val =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  have hfactor :
      (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) =
        (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
          (PowerSeries.X : PowerSeries ℤ) ^ j) * (1 - PowerSeries.X) ^ m := by
    simp_rw [← geom_sum_mul_neg]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hfactor, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  rw [(PowerSeries.invOneSubPow ℤ m).inv_val, mul_one]

theorem regular_sequence_series_geometric [Fintype σ]
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ∏ i ∈ Finset.range rs.length, ∑ j ∈ Finset.range (degreeAt degrees i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  have h := regular_prefix_series rs degrees hhom hreg rs.length le_rfl
  simp only [List.take_length] at h
  rw [h, sectionHilbertSeries_bot hσ, ← hlen]
  exact degree_factors_mul_invOneSubPow (degreeAt degrees) rs.length

end PiExponentJets.W64

end OAI
