import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.SiegelZeros.Hilbert.HilbertZeroVariables

namespace OAI

section

namespace SiegelZeros.W20

section Ring

variable {R : Type*} [CommRing R]

theorem prefixIdeal_succ (rs : List R) (i : Fin rs.length) :
    Ideal.ofList (rs.take (i.val + 1)) =
      Ideal.span {rs[i]} ⊔ Ideal.ofList (rs.take i.val) := by
  rw [List.take_succ_eq_append_getElem i.isLt, Ideal.ofList_append,
    Ideal.ofList_singleton, sup_comm]
  simp only [Fin.getElem_fin]

theorem regular_next_mod_prefix (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take i.val)) rs[i]) := by
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have htop : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) =
      Ideal.ofList (rs.take i.val) := by
    exact (Ideal.ofList (rs.take i.val)).mul_top
  rw [htop] at hsmul
  intro x y hxy
  apply hsmul
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm,
    Fin.getElem_fin] using hxy

theorem prefixIdeal_zero (rs : List R) : Ideal.ofList (rs.take 0) = ⊥ := by
  simp

theorem prefixIdeal_length (rs : List R) :
    Ideal.ofList (rs.take rs.length) = Ideal.ofList rs := by
  simp

end Ring

section Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prefixIdeal_homogeneous
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i)) (n : ℕ) :
    (Ideal.ofList (rs.take n)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hf)
  exact ⟨degrees ⟨i, hi⟩, hhom ⟨i, hi⟩⟩

theorem regular_prefix_hilbert_recurrence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (i : Fin rs.length) (n : ℕ) :
    Module.finrank k
        (WeightedTorusJets.W64.quotientSection
          (Ideal.ofList (rs.take (i.val + 1))) (n + degrees i)) +
      Module.finrank k
        (WeightedTorusJets.W64.quotientSection (Ideal.ofList (rs.take i.val)) n) =
      Module.finrank k
        (WeightedTorusJets.W64.quotientSection
          (Ideal.ofList (rs.take i.val)) (n + degrees i)) := by
  rw [prefixIdeal_succ rs i]
  exact WeightedTorusJets.W64.regular_hilbert_step
    (Ideal.ofList (rs.take i.val))
    (prefixIdeal_homogeneous rs degrees hhom i.val)
    rs[i] (hhom i) (regular_next_mod_prefix rs hreg i) n

end Polynomial

end SiegelZeros.W20

end

namespace SiegelZeros

section

namespace WeightedTorusJets.W64

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
    rw [SiegelZeros.W20.prefixIdeal_succ rs ⟨n, hlt⟩]
    simp only [Fin.getElem_fin]
    have hh : (rs[n]'hlt).IsHomogeneous (degrees ⟨n, hlt⟩) := by
      simpa only [Fin.getElem_fin] using hhom ⟨n, hlt⟩
    have hr : IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take n)) (rs[n]'hlt)) := by
      simpa only [Fin.getElem_fin] using
        SiegelZeros.W20.regular_next_mod_prefix rs hreg ⟨n, hlt⟩
    rw [sectionHilbertSeries_regular_step _
      (SiegelZeros.W20.prefixIdeal_homogeneous rs degrees hhom n)
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

end WeightedTorusJets.W64

end

end SiegelZeros

end OAI
