import OAI.NumberTheory.PiExponent.Jets.DifferentialConstant
import OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis
import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero

namespace OAI

noncomputable section

namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C : Type*} [Field C] [CharZero C] [IsAlgClosed C] {m : ℕ}

abbrev primeNormalProjection (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :=
  (polynomialTangent (polynomialResidueMap Q) Q).mkQ

noncomputable def primeCoordinateNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q (Pi.basisFun (PolynomialResidueField Q) _ i)

noncomputable def primeLogarithmicNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hy : polynomialResidueMap Q (X (0 : Fin (m + 1))) ≠ 0) :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q
    (frameBasis m (polynomialResidueMap Q (X 0)) hy i)

theorem zeroth_coordinate_constant_of_normal_separation
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hy : polynomialResidueMap Q (X (0 : Fin (m + 1))) ≠ 0)
    (hq : primeNormalProjection Q ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := PolynomialResidueField Q) (primeCoordinateNormals Q) A →
      IsNormalBasis (K := PolynomialResidueField Q) (primeLogarithmicNormals Q hy) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  let φ := polynomialResidueMap Q
  let q := primeNormalProjection Q
  have : Algebra.EssFiniteType C (PolynomialResidueField Q) :=
    polynomialResidueField_essFiniteType Q
  have hd := normal_basis_differential_dichotomy m (φ (X 0)) hy q
    (Submodule.mkQ_surjective _) hq hexclude
  rcases hd with hzero | ⟨i, hlog⟩
  · have hD : KaehlerDifferential.D C (PolynomialResidueField Q) (φ (X 0)) = 0 :=
      differential_eq_zero_of_polynomialTangent φ Q
        (polynomialResidueMap_eq_zero Q) 0 (fun t ht =>
          hzero t ((Submodule.Quotient.mk_eq_zero _).mpr ht))
    obtain ⟨c, hc⟩ := constant_of_differential_eq_zero (φ (X 0)) hD
    exact ⟨c, coordinate_sub_constant_mem_prime Q 0 c hc⟩
  · obtain ⟨c, hc⟩ := constant_of_prime_polynomialTangent Q i.succ 0
      (fun t ht => hlog t ((Submodule.Quotient.mk_eq_zero _).mpr ht))
    exact ⟨c, coordinate_sub_constant_mem_prime Q 0 c hc⟩

theorem zeroth_coordinate_constant_of_normal_weight_comparison
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hy : polynomialResidueMap Q (X (0 : Fin (m + 1))) ≠ 0)
    (hq : primeNormalProjection Q ≠ 0)
    (w cost : Fin (m + 1) → ℝ) (M : ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := PolynomialResidueField Q) (primeCoordinateNormals Q) A →
      IsNormalBasis (K := PolynomialResidueField Q) (primeLogarithmicNormals Q hy) B →
      (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  apply zeroth_coordinate_constant_of_normal_separation Q hy hq
  exact weighted_normalBasis_exclusion (primeCoordinateNormals Q)
    (primeLogarithmicNormals Q hy) w cost M hcomparison hseparated

theorem prime_component_constant_of_weight_comparison
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) (hy : X (0 : Fin (m + 1)) ∉ Q)
    (w cost : Fin (m + 1) → ℝ) (M : ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := PolynomialResidueField Q) (primeCoordinateNormals Q) A →
      IsNormalBasis (K := PolynomialResidueField Q)
        (primeLogarithmicNormals Q (fun h => hy ((polynomialResidueMap_eq_zero_iff Q _).mp h))) B →
      (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  exact zeroth_coordinate_constant_of_normal_weight_comparison Q
    (fun h => hy ((polynomialResidueMap_eq_zero_iff Q _).mp h))
    (polynomialPrimeNormal_mkQ_ne_zero Q hQ) w cost M hcomparison hseparated

omit [CharZero C] [IsAlgClosed C] in
theorem constant_coordinate_eq_one_of_center
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) (a : Fin (m + 1) → C)
    (ha : a 0 = 1) (hpoint : ∀ p ∈ Q, MvPolynomial.eval a p = 0)
    (hconstant : ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q) :
    X (0 : Fin (m + 1)) - 1 ∈ Q := by
  obtain ⟨c, hc⟩ := hconstant
  have he := hpoint _ hc
  simp only [eval_sub, eval_X, eval_C, ha, sub_eq_zero] at he
  simpa only [← he, map_one] using hc

end PiExponent

end

end OAI
