import OAI.NumberTheory.SiegelZeros.Estimates.ComponentMultiplicityBound
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularParameterSelection

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem actualHP_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP (Ideal.ofList rs) hI = regularSequenceHilbertPolynomial rs degrees := by
  apply actualHP_unique _ hI _
    (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree
  intro n hn
  exact regularSequenceHilbertPolynomial_eventually_exact
    (lt_of_le_of_lt (Nat.zero_le _) hlen) rs degrees hhom hreg hlen.le n hn

omit [Fintype σ] in
theorem regular_degreeAt_product_ne_zero
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp only [degreeAt, dite_eq_left hi']
  exact Nat.ne_of_gt (SiegelZeros.W20.regular_homogeneous_degrees_pos
    rs degrees hhom hreg ⟨i, hi'⟩)

theorem actualHP_regular_sequence_natDegree
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (actualHP (Ideal.ofList rs) hI).natDegree = Fintype.card σ - rs.length - 1 := by
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  have hp : (rationalDegreePolynomial (degreeAt degrees) rs.length).eval 1 ≠ 0 := by
    rw [rationalDegreePolynomial_eval_one]
    exact_mod_cast regular_degreeAt_product_ne_zero rs degrees hhom hreg
  exact (hilbertPolynomial_degree_and_leading _ _ (Nat.sub_pos_of_lt hlen) hp).1

theorem actualMultiplicity_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualMultiplicity (Ideal.ofList rs) hI (actualHP (Ideal.ofList rs) hI).natDegree =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  rw [actualHP_regular_sequence_natDegree rs degrees hhom hreg hlen hI]
  unfold actualMultiplicity
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  exact regularSequenceHilbertPolynomial_multiplicity rs degrees hlen

theorem regular_sequence_component_length_le_degree_product
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQhom : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ (Ideal.ofList rs).minimalPrimes)
    (v : σ) (hv : MvPolynomial.X v ∉ Q)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ Q) =
      (Fintype.card σ - rs.length : ℕ)) :
    ∃ m : ℕ,
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ (Ideal.ofList rs).map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m ∧
      m ≤ ∏ i ∈ Finset.range rs.length, degreeAt degrees i := by
  have hI : (Ideal.ofList rs).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
    simpa only [List.take_length] using
      SiegelZeros.W20.prefixIdeal_homogeneous rs degrees hhom rs.length
  obtain ⟨N, hN⟩ := actualHP_eventually Q hQhom
  have hQdim := W24.prime_hilbert_natDegree_add_one_eq_krullDim
    Q hQhom v hv (actualHP Q hQhom) (N+1) (fun n hn => (hN n (by omega)).symm)
  have hQdeg : (actualHP Q hQhom).natDegree + 1 = Fintype.card σ - rs.length := by
    exact_mod_cast hQdim.trans hdim
  have hdegree : (actualHP Q hQhom).natDegree =
      (actualHP (Ideal.ofList rs) hI).natDegree := by
    rw [actualHP_regular_sequence_natDegree rs degrees hhom hreg hlen hI]
    omega
  obtain ⟨m, hm, hpositive, hbound⟩ :=
    component_multiplicity_bound (Ideal.ofList rs) Q hI hQhom hQ v hv hdegree
  refine ⟨m, hm, ?_⟩
  have hprod := actualMultiplicity_regular_sequence rs degrees hhom hreg hlen hI
  rw [hprod] at hbound
  have hsmall : (m : ℚ) ≤ (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
    have hmpos : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    nlinarith
  exact_mod_cast hsmall

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
