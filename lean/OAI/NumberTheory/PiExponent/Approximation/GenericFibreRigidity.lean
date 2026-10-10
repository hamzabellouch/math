import OAI.NumberTheory.PiExponent.Approximation.FibreNormalRigidity
import OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity

namespace OAI

noncomputable section

namespace PiExponent

open Module MvPolynomial NormalBasisRigidity

variable {C E ι : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E]
  [Fintype ι] [LinearOrder ι]

abbrev genericCoordinateNormals (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : ι → PolynomialNormal φ Q :=
  fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)

omit [LinearOrder ι] in
theorem coordinate_constant_of_generic_unique_normal_basis
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hunique : ∀ A B : Finset ι,
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) A →
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) B → A = B) :
    ∃ i : ι, ∃ c : C, X i - MvPolynomial.C c ∈ Q := by
  let q := (polynomialTangent φ Q).mkQ
  let b := Pi.basisFun E ι
  have hq : q ≠ 0 := polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ
  have hex : ∃ i, q (b i) ≠ 0 := by
    by_contra! h
    apply hq
    exact b.ext h
  obtain ⟨i, hi⟩ := hex
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing (fun j => q (b j))
    (polynomialNormal_span φ Q b) i hi
  have hmand : ∀ B, IsNormalBasis (K := E) (fun j => q (b j)) B → i ∈ B := by
    intro B hB
    rw [← hunique A B hA hB]
    exact hiA
  have htangent : ∀ t ∈ polynomialTangent φ Q, t i = 0 := by
    intro t ht
    have hh := mandatory_coordinate_eq_zero b q (polynomialNormal_span φ Q b)
      i hmand t ((Submodule.Quotient.mk_eq_zero _).mpr ht)
    simpa only [b, Pi.basisFun_repr] using hh
  have hD := differential_eq_zero_of_polynomialTangent φ Q
    (fun p hp => (hker p).mpr hp) i htangent
  obtain ⟨c, hc⟩ := constant_of_differential_eq_zero (φ (X i)) hD
  refine ⟨i, c, (hker _).mp ?_⟩
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

theorem coordinate_constant_of_generic_normal_separation
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hexclude : ∀ A B : Finset ι,
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) A →
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) B →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ i : ι, ∃ c : C, X i - MvPolynomial.C c ∈ Q := by
  apply coordinate_constant_of_generic_unique_normal_basis φ Q hker hQ
  exact normalBasis_unique_of_discrepancy_excluded _ hexclude

theorem coordinate_constant_of_generic_normal_weight_comparison
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (w cost : ι → ℝ) (M : ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) A →
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) B →
      (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset ι, A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ i : ι, ∃ c : C, X i - MvPolynomial.C c ∈ Q := by
  apply coordinate_constant_of_generic_normal_separation φ Q hker hQ
  intro A B hA hB i hiA hiB hlarge
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hiA hiB hlarge)

theorem generic_normal_separation_at_most_one_center {J : Type*}
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hexclude : ∀ A B : Finset ι,
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) A →
      IsNormalBasis (K := E) (genericCoordinateNormals φ Q) B →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (centers : J → ι → C) (hinj : ∀ i, Function.Injective (fun j => centers j i))
    (j k : J)
    (hj : ∀ p ∈ Q, MvPolynomial.eval (centers j) p = 0)
    (hk : ∀ p ∈ Q, MvPolynomial.eval (centers k) p = 0) : j = k := by
  obtain ⟨i, c, hc⟩ := coordinate_constant_of_generic_normal_separation φ Q hker hQ hexclude
  exact coordinate_constant_at_most_one_center Q centers i c hc (hinj i) j k hj hk

end PiExponent

end

end OAI
