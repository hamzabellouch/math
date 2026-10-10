import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalRigidity

namespace OAI

noncomputable section
namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C ι : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem coordinate_constant_of_unique_normal_basis
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (hq : (polynomialTangent (polynomialResidueMap Q) Q).mkQ ≠ 0)
    (hunique : ∀ A B : Finset ι,
      IsNormalBasis (K := PolynomialResidueField Q)
        (fun j => (polynomialTangent (polynomialResidueMap Q) Q).mkQ
          (Pi.basisFun (PolynomialResidueField Q) ι j)) A →
      IsNormalBasis (K := PolynomialResidueField Q)
        (fun j => (polynomialTangent (polynomialResidueMap Q) Q).mkQ
          (Pi.basisFun (PolynomialResidueField Q) ι j)) B → A = B) :
    ∃ i : ι, ∃ c : C, X i - MvPolynomial.C c ∈ Q := by
  let φ := polynomialResidueMap Q
  let q := (polynomialTangent φ Q).mkQ
  let b := Pi.basisFun (PolynomialResidueField Q) ι
  have hex : ∃ i, q (b i) ≠ 0 := by
    by_contra! h
    apply hq
    exact b.ext h
  obtain ⟨i, hi⟩ := hex
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing (fun j => q (b j))
    (polynomialNormal_span φ Q b) i hi
  have hmand : ∀ B, IsNormalBasis (K := PolynomialResidueField Q) (fun j => q (b j)) B → i ∈ B := by
    intro B hB
    rw [← hunique A B hA hB]
    exact hiA
  have htangent : ∀ t ∈ polynomialTangent φ Q, t i = 0 := by
    intro t ht
    have hh := mandatory_coordinate_eq_zero b q (polynomialNormal_span φ Q b)
      i hmand t ((Submodule.Quotient.mk_eq_zero _).mpr ht)
    simpa only [b, Pi.basisFun_repr] using hh
  have hD := differential_eq_zero_of_polynomialTangent φ Q
    (polynomialResidueMap_eq_zero Q) i htangent
  have : Algebra.EssFiniteType C (PolynomialResidueField Q) :=
    polynomialResidueField_essFiniteType Q
  obtain ⟨c, hc⟩ := constant_of_differential_eq_zero (φ (X i)) hD
  exact ⟨i, c, coordinate_sub_constant_mem_prime Q i c hc⟩

theorem coordinate_constant_of_normal_discrepancy_excluded
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (hq : (polynomialTangent (polynomialResidueMap Q) Q).mkQ ≠ 0)
    (hexclude : ∀ A B : Finset ι,
      IsNormalBasis (K := PolynomialResidueField Q)
        (fun j => (polynomialTangent (polynomialResidueMap Q) Q).mkQ
          (Pi.basisFun (PolynomialResidueField Q) ι j)) A →
      IsNormalBasis (K := PolynomialResidueField Q)
        (fun j => (polynomialTangent (polynomialResidueMap Q) Q).mkQ
          (Pi.basisFun (PolynomialResidueField Q) ι j)) B →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ i : ι, ∃ c : C, X i - MvPolynomial.C c ∈ Q := by
  apply coordinate_constant_of_unique_normal_basis Q hq
  exact normalBasis_unique_of_discrepancy_excluded _ hexclude

omit [CharZero C] [IsAlgClosed C] [Fintype ι] [LinearOrder ι] in

theorem coordinate_constant_at_most_one_center {J : Type*}
    (Q : Ideal (MvPolynomial ι C)) (centers : J → ι → C)
    (i : ι) (c : C) (hc : X i - MvPolynomial.C c ∈ Q)
    (hinj : Function.Injective (fun j => centers j i))
    (j k : J)
    (hj : ∀ p ∈ Q, MvPolynomial.eval (centers j) p = 0)
    (hk : ∀ p ∈ Q, MvPolynomial.eval (centers k) p = 0) : j = k := by
  have hjc := hj _ hc
  have hkc := hk _ hc
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hjc hkc
  exact hinj (hjc.trans hkc.symm)

end PiExponent

end

end OAI
