import Mathlib.RingTheory.Polynomial.Ideal
import OAI.AlgebraicGeometry.PlaneCurves.CoefficientIdeals
import OAI.AlgebraicGeometry.PlaneCurves.RationalKernels
import OAI.AlgebraicGeometry.PlaneCurves.SquareLinear

namespace OAI

/-!
# Principal restrictions and local normal coefficient families
-/

section

/-!
# Restriction to the principal hypersurface quotient
-/

namespace Nagata.W18

open scoped BigOperators

/-- A factorization that cannot be extended by another `G` has a remainder
not divisible by `G`. This implication needs no domain assumption. -/
theorem not_dvd_remainder_of_maximal_power {A : Type*} [CommRing A]
    (G S T : A) (j : ℕ) (hfactor : S = G ^ j * T)
    (hmaximal : ¬G ^ (j + 1) ∣ S) : ¬G ∣ T := by
  rintro ⟨q, hq⟩
  apply hmaximal
  refine ⟨q, ?_⟩
  rw [hfactor, hq, pow_succ, mul_assoc]

/-- Maximal extracted powers give nonzero residues in the genuine quotient. -/
theorem residue_ne_zero_of_maximal_power {A : Type*} [CommRing A]
    (G S T : A) (j : ℕ) (hfactor : S = G ^ j * T)
    (hmaximal : ¬G ^ (j + 1) ∣ S) :
    Ideal.Quotient.mk (Ideal.span ({G} : Set A)) T ≠ 0 := by
  intro hz
  exact not_dvd_remainder_of_maximal_power G S T j hfactor hmaximal
    ((Ideal.Quotient.eq_zero_iff_dvd G T).mp hz)

/-- The direct form needed when maximal factorization returns `¬G ∣ T`. -/
theorem residue_ne_zero_of_not_dvd {A : Type*} [CommRing A]
    (G T : A) (hT : ¬G ∣ T) :
    Ideal.Quotient.mk (Ideal.span ({G} : Set A)) T ≠ 0 := by
  intro hz
  exact hT ((Ideal.Quotient.eq_zero_iff_dvd G T).mp hz)

/-- A prime hypersurface ideal supplies the expected domain structure.
The preceding nonzero-residue statements hold even without this hypothesis. -/
theorem principal_quotient_isDomain {A : Type*} [CommRing A]
    (G : A) (hprime : (Ideal.span ({G} : Set A)).IsPrime) :
    IsDomain (A ⧸ Ideal.span ({G} : Set A)) := by
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr hprime

/-- The selected normal polynomial is nonzero over the hypersurface quotient. -/
theorem principal_normal_polynomial_ne_zero {A : Type*} [CommRing A]
    (s : Finset ℕ) (G : A) (S T : ℕ → A) (j : ℕ → ℕ) (u : ℕ)
    (hne : s.Nonempty) (hweight : ∀ a ∈ s, a + j a = u)
    (hfactor : ∀ a ∈ s, S a = G ^ j a * T a)
    (hmaximal : ∀ a ∈ s, ¬G ^ (j a + 1) ∣ S a) :
    (∑ a ∈ s, Polynomial.monomial (j a)
      (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T a))) ≠ 0 := by
  apply diagonal_monomial_sum_ne_zero s j _ u hweight hne
  intro a ha
  exact residue_ne_zero_of_maximal_power G (S a) (T a) (j a)
    (hfactor a ha) (hmaximal a ha)

/-- Direct interface for maximal-factorization APIs returning indivisible remainders. -/
theorem principal_diagonal_polynomial_ne_zero {A : Type*} [CommRing A]
    (s : Finset ℕ) (G : A) (T : ℕ → A) (j : ℕ → ℕ) (u : ℕ)
    (hne : s.Nonempty) (hweight : ∀ a ∈ s, a + j a = u)
    (hT : ∀ a ∈ s, ¬G ∣ T a) :
    (∑ a ∈ s, Polynomial.monomial (j a)
      (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T a))) ≠ 0 := by
  apply diagonal_monomial_sum_ne_zero s j _ u hweight hne
  intro a ha
  exact residue_ne_zero_of_not_dvd G (T a) (hT a ha)

/-- Specialization to genuine multivariable coordinate polynomials. -/
theorem mvPolynomial_normal_polynomial_ne_zero {K σ : Type*} [Field K]
    (s : Finset ℕ) (G : MvPolynomial σ K) (S T : ℕ → MvPolynomial σ K)
    (j : ℕ → ℕ) (u : ℕ)
    (hne : s.Nonempty) (hweight : ∀ a ∈ s, a + j a = u)
    (hfactor : ∀ a ∈ s, S a = G ^ j a * T a)
    (hmaximal : ∀ a ∈ s, ¬G ^ (j a + 1) ∣ S a) :
    (∑ a ∈ s, Polynomial.monomial (j a)
      (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial σ K))) (T a))) ≠ 0 :=
  principal_normal_polynomial_ne_zero s G S T j u hne hweight hfactor hmaximal

/-- A chart ring map annihilating `G` annihilates its principal ideal. -/
theorem restriction_annihilates_principal {A B : Type*} [CommRing A] [CommRing B]
    (G : A) (f : A →+* B) (hG : f G = 0) :
    ∀ a ∈ Ideal.span ({G} : Set A), f a = 0 := by
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
  rw [map_mul, hG, zero_mul]

/-- The induced chart restriction on the genuine hypersurface quotient. -/
def principalRestriction {A B : Type*} [CommRing A] [CommRing B]
    (G : A) (f : A →+* B) (hG : f G = 0) :
    A ⧸ Ideal.span ({G} : Set A) →+* B :=
  Ideal.Quotient.lift _ f (restriction_annihilates_principal G f hG)

/-- A quotient coefficient restricts to the original coefficient's chart value. -/
theorem principalRestriction_residue {A B : Type*} [CommRing A] [CommRing B]
    (G : A) (f : A →+* B) (hG : f G = 0) (a : A) :
    principalRestriction G f hG (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) a) =
      f a := rfl

/-- Extracting a selected coefficient and then restricting agrees with its
original chart restriction. No injectivity of the chart ring map is assumed. -/
theorem selected_coefficient_restriction {A B : Type*} [CommRing A] [CommRing B]
    (s : Finset ℕ) (G : A) (T : ℕ → A) (j : ℕ → ℕ) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u)
    (f : A →+* B) (hG : f G = 0) (a : ℕ) (ha : a ∈ s) :
    principalRestriction G f hG
      ((∑ b ∈ s, Polynomial.monomial (j b)
        (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T b))).coeff (j a)) =
      f (T a) := by
  rw [coefficient_of_injective_monomial_sum s j _
    (exponent_injective_on_diagonal s j u hweight) a ha]
  exact principalRestriction_residue G f hG (T a)

end Nagata.W18

end

section

noncomputable section
namespace Nagata.W18

variable {K : Type*} [CommRing K]

/-- Coordinate 0 is the base variable U; coordinate 1 is the fiber variable W. -/
def bivariateToNested : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.C Polynomial.X, Polynomial.X]

/-- The inverse substitution sends inner X to coordinate 0 and outer X to 1. -/
def nestedToBivariate : Polynomial (Polynomial K) →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)

theorem nestedToBivariate_comp_bivariateToNested :
    (nestedToBivariate (K := K)).comp bivariateToNested = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bivariateToNested, nestedToBivariate]
  · intro i
    fin_cases i <;> simp [bivariateToNested, nestedToBivariate]

theorem bivariateToNested_comp_nestedToBivariate :
    (bivariateToNested (K := K)).comp nestedToBivariate = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro p
    have h : bivariateToNested.comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2))) =
        (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)) := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [bivariateToNested]
      · simp [bivariateToNested]
    simpa [nestedToBivariate] using RingHom.congr_fun h p
  · simp [nestedToBivariate, bivariateToNested]

/-- The two concrete polynomial coordinate rings are isomorphic. -/
def bivariateNestedEquiv : MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  RingEquiv.ofRingHom bivariateToNested nestedToBivariate
    bivariateToNested_comp_nestedToBivariate nestedToBivariate_comp_bivariateToNested

/-- Explicit compatibility of both coordinate evaluations. -/
theorem eval_bivariateToNested (a c : K) (F : MvPolynomial (Fin 2) K) :
    ((bivariateToNested F).eval (Polynomial.C c)).eval a =
      MvPolynomial.eval ![a, c] F := by
  have h : (Polynomial.evalRingHom a).comp
      ((Polynomial.evalRingHom (Polynomial.C c)).comp bivariateToNested) =
      MvPolynomial.eval ![a, c] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivariateToNested]
    · intro i
      fin_cases i <;> simp [bivariateToNested]
  exact RingHom.congr_fun h F

/-- The generated point ideal is exactly the evaluation kernel, not a
substitute notion of multiplicity. -/
theorem nestedPointIdeal_mem_iff (a c : K) (H : Polynomial (Polynomial K)) :
    H ∈ nestedPointIdeal a c ↔ (H.eval (Polynomial.C c)).eval a = 0 :=
  Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero

theorem pointIdeal_map_bivariateNestedEquiv (a c : K) :
    (Nagata.AffineMultiplicity.pointIdeal ![a, c]).map bivariateNestedEquiv =
      nestedPointIdeal a c := by
  ext H
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨F, hF, rfl⟩
    rw [nestedPointIdeal_mem_iff]
    exact (eval_bivariateToNested a c F).trans
      ((Nagata.AffineMultiplicity.pointIdeal_mem_iff _ _).mp hF)
  · intro hH
    refine ⟨bivariateNestedEquiv.symm H, ?_, bivariateNestedEquiv.apply_symm_apply H⟩
    rw [Nagata.AffineMultiplicity.pointIdeal_mem_iff,
      ← eval_bivariateToNested a c]
    change ((bivariateNestedEquiv (bivariateNestedEquiv.symm H)).eval
      (Polynomial.C c)).eval a = 0
    rw [bivariateNestedEquiv.apply_symm_apply]
    exact (nestedPointIdeal_mem_iff a c H).mp hH

/-- The source ordinary multiplicity hypothesis supplies the nested ideal power. -/
theorem nested_order_of_affine_order (a c : K) (m : ℕ)
    (F : MvPolynomial (Fin 2) K)
    (hF : Nagata.AffineMultiplicity.orderAtLeast ![a, c] m F) :
    bivariateToNested F ∈ (nestedPointIdeal a c) ^ m := by
  have h := Ideal.mem_map_of_mem bivariateNestedEquiv hF
  rw [Ideal.map_pow, pointIdeal_map_bivariateNestedEquiv] at h
  exact h

theorem affine_top_coefficient_base_divisibility (a c : K) (m J : ℕ)
    (F : MvPolynomial (Fin 2) K)
    (hF : Nagata.AffineMultiplicity.orderAtLeast ![a, c] m F)
    (hJ : (bivariateToNested F).natDegree ≤ J) :
    (Polynomial.X - Polynomial.C a) ^ (m - J) ∣ (bivariateToNested F).coeff J :=
  top_coefficient_base_divisibility _ a c m J hJ (nested_order_of_affine_order a c m F hF)

theorem affine_fiber_power_divides (a c : K) (m : ℕ)
    (F : MvPolynomial (Fin 2) K)
    (hF : Nagata.AffineMultiplicity.orderAtLeast ![a, c] m F) :
    (Polynomial.X - Polynomial.C c) ^ m ∣ fiberRestriction a (bivariateToNested F) :=
  fiber_power_divides_of_surface_order _ a c m (nested_order_of_affine_order a c m F hF)

end Nagata.W18

end
end

section

/-! Finite coefficient-list wrappers and the square-case fiber comparison.
The arbitrary-displacement assertion concerns the top coefficient only.
All coefficient orders are asserted only at zero displacement. -/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Nagata.W18

/-- The actual finite normal polynomial `Σ_{j≤J} q_j(U) W^j`. -/
def normalCoefficientFamily {K : Type*} [CommRing K]
    (J : ℕ) (q : ℕ → Polynomial K) : Polynomial (Polynomial K) :=
  ∑ j ∈ Finset.range (J + 1), monomial j (q j)

/-- Coefficient extraction identifies the finite list with the polynomial. -/
theorem normalCoefficientFamily_coeff {K : Type*} [CommRing K]
    (J : ℕ) (q : ℕ → Polynomial K) (j : ℕ) (hj : j ≤ J) :
    (normalCoefficientFamily J q).coeff j = q j := by
  apply coefficient_of_injective_monomial_sum (Finset.range (J + 1)) id q
    (fun _ _ _ _ h => h) j
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

/-- The finite list has the required fiber degree bound, even with zero coefficients. -/
theorem normalCoefficientFamily_natDegree_le {K : Type*} [CommRing K]
    (J : ℕ) (q : ℕ → Polynomial K) :
    (normalCoefficientFamily J q).natDegree ≤ J := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le (q j)).trans (by simpa using Finset.mem_range.mp hj)

/-- Surface order at arbitrary `(a,c)` forces order `m-J` of the top list coefficient. -/
theorem family_top_base_divisibility {K : Type*} [CommRing K]
    (J : ℕ) (q : ℕ → Polynomial K) (a c : K) (m : ℕ)
    (hH : normalCoefficientFamily J q ∈ (nestedPointIdeal a c) ^ m) :
    (X - C a) ^ (m - J) ∣ q J := by
  have h := top_coefficient_base_divisibility (normalCoefficientFamily J q) a c m J
    (normalCoefficientFamily_natDegree_le J q) hH
  rwa [normalCoefficientFamily_coeff J q J le_rfl] at h

/-- At zero fiber displacement, every coefficient has the base-order bound.
No degree assumption is needed for this statement. -/
theorem all_coefficients_base_divisibility_at_zero {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a : K) (m : ℕ)
    (hH : H ∈ (nestedPointIdeal a 0) ^ m) (j : ℕ) :
    (X - C a) ^ (m - j) ∣ H.coeff j := by
  apply coefficient_dvd_of_coordinate_ideal_power (X - C a) m H _ j
  simpa only [nestedPointIdeal, map_zero, sub_zero] using hH

/-- Finite-list version of the nine-zero coefficient condition. -/
theorem family_coefficient_base_divisibility_at_zero {K : Type*} [CommRing K]
    (J : ℕ) (q : ℕ → Polynomial K) (a : K) (m j : ℕ) (hj : j ≤ J)
    (hH : normalCoefficientFamily J q ∈ (nestedPointIdeal a 0) ^ m) :
    (X - C a) ^ (m - j) ∣ q j := by
  have h := all_coefficients_base_divisibility_at_zero (normalCoefficientFamily J q) a m hH j
  rwa [normalCoefficientFamily_coeff J q j hj] at h

/-- The actual surface ideal condition supplies the square-case penultimate
fiber coefficient identity, retaining the nonzero leading coefficient. -/
theorem surface_order_penultimate_coefficient {K : Type*} [Field K]
    (H : Polynomial (Polynomial K)) (a c : K) (m : ℕ) (hm : 0 < m)
    (hdeg : H.natDegree ≤ m) (hH : H ∈ (nestedPointIdeal a c) ^ m)
    (htop : (H.coeff m).eval a ≠ 0) :
    (H.coeff (m - 1)).eval a = (-(m : K) * (H.coeff m).eval a) * c := by
  have h := Nagata.Workers.W24.polynomial_penultimate_coefficient_scalar
    (fiberRestriction a H) c m hm ((fiberRestriction_natDegree_le H a).trans hdeg)
    (fiber_power_divides_of_surface_order H a c m hH)
  rwa [fiberRestriction_coeff, fiberRestriction_leadingCoeff H a m hdeg htop] at h

/-- Finite normal coefficient list version of the square-case fiber identity. -/
theorem family_penultimate_coefficient {K : Type*} [Field K]
    (q : ℕ → Polynomial K) (a c : K) (m : ℕ) (hm : 0 < m)
    (hH : normalCoefficientFamily m q ∈ (nestedPointIdeal a c) ^ m)
    (htop : (q m).eval a ≠ 0) :
    (q (m - 1)).eval a = (-(m : K) * (q m).eval a) * c := by
  have h := surface_order_penultimate_coefficient (normalCoefficientFamily m q)
    a c m hm (normalCoefficientFamily_natDegree_le m q) hH
    (by rwa [normalCoefficientFamily_coeff m q m le_rfl])
  rwa [normalCoefficientFamily_coeff m q m le_rfl,
    normalCoefficientFamily_coeff m q (m - 1) (Nat.sub_le _ _)] at h

end Nagata.W18

end
end

end OAI
