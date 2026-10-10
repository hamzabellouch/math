import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial KaehlerDifferential

section PolynomialMap
variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι]

theorem derivation_polynomial_map (φ : MvPolynomial ι C →ₐ[C] E)
    (d : Derivation C E E) (p : MvPolynomial ι C) :
    d (φ p) = ∑ i, φ (pderiv i p) * d (φ (X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp,
      map_add, pderiv_X, Finset.sum_add_distrib, add_mul, mul_assoc]
    simp only [← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

def polynomialJacobian (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : (ι → E) →ₗ[E] (Q → E) where
  toFun t p := ∑ i, φ (pderiv i p.1) * t i
  map_add' t u := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a t := by ext p; simp [Finset.mul_sum, mul_left_comm]

def polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : Submodule E (ι → E) :=
  LinearMap.ker (polynomialJacobian φ Q)

abbrev PolynomialNormal (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) := (ι → E) ⧸ polynomialTangent φ Q

theorem derivation_mem_polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) (hQ : ∀ p ∈ Q, φ p = 0)
    (d : Derivation C E E) :
    (fun i => d (φ (X i))) ∈ polynomialTangent φ Q := by
  change polynomialJacobian φ Q (fun i => d (φ (X i))) = 0
  ext p
  change (∑ i, φ (pderiv i p.1) * d (φ (X i))) = 0
  rw [← derivation_polynomial_map, hQ p.1 p.2, map_zero]

theorem differential_relation_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (a : ι → E)
    (h : ∀ t ∈ polynomialTangent φ Q, ∑ i, a i * t i = 0) :
    (∑ i, a i • D C E (φ (X i))) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  have hd := h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)
  change (∑ i, a i * l (D C E (φ (X i)))) = 0 at hd
  simpa only [map_sum, map_smul, smul_eq_mul] using hd

theorem logarithmic_differential_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i j : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = t j / φ (X j)) :
    D C E (φ (X i)) = (φ (X j))⁻¹ • D C E (φ (X j)) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  have hd := h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)
  change l (D C E (φ (X i))) = l (D C E (φ (X j))) / φ (X j) at hd
  simpa only [map_sub, map_smul, smul_eq_mul, div_eq_mul_inv,
    sub_eq_zero, mul_comm] using hd

theorem differential_eq_zero_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = 0) :
    D C E (φ (X i)) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  exact h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)

theorem polynomialNormal_span
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (b : Module.Basis ι E (ι → E)) :
    Submodule.span E (Set.range (fun i => (polynomialTangent φ Q).mkQ (b i))) = ⊤ := by
  rw [Set.range_comp', ← Submodule.map_span, b.span_eq, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

end PolynomialMap

variable {C ι : Type*} [Field C] [Fintype ι]

abbrev PolynomialResidueField (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :=
  FractionRing (MvPolynomial ι C ⧸ Q)

def polynomialResidueMap (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    MvPolynomial ι C →ₐ[C] PolynomialResidueField Q :=
  (IsScalarTower.toAlgHom C (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)).comp
    (Ideal.Quotient.mkₐ C Q)

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) (hp : p ∈ Q) : polynomialResidueMap Q p = 0 := by
  change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    (Ideal.Quotient.mk Q p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero_iff (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) : polynomialResidueMap Q p = 0 ↔ p ∈ Q := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
      (Ideal.Quotient.mk Q p) = 0 at h
    simpa only [map_zero] using h
  · exact polynomialResidueMap_eq_zero Q p

omit [Fintype ι] in

theorem coordinate_sub_constant_mem_prime
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (j : ι) (c : C)
    (h : algebraMap C (PolynomialResidueField Q) c = polynomialResidueMap Q (X j)) :
    X j - MvPolynomial.C c ∈ Q := by
  apply (polynomialResidueMap_eq_zero_iff Q _).mp
  simp only [map_sub, MvPolynomial.algHom_C, h, sub_self]

theorem polynomialResidueField_essFiniteType (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    Algebra.EssFiniteType C (PolynomialResidueField Q) := by infer_instance

theorem constant_of_prime_polynomialTangent
    [CharZero C] [IsAlgClosed C] (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (i j : ι)
    (h : ∀ t ∈ polynomialTangent (polynomialResidueMap Q) Q,
      t i = t j / polynomialResidueMap Q (X j)) :
    ∃ c : C, algebraMap C (PolynomialResidueField Q) c = polynomialResidueMap Q (X j) := by
  have : Algebra.EssFiniteType C (PolynomialResidueField Q) :=
    polynomialResidueField_essFiniteType Q
  exact constant_of_logarithmic_differential _ _
    (logarithmic_differential_of_polynomialTangent (polynomialResidueMap Q) Q
      (polynomialResidueMap_eq_zero Q) i j h)

end PiExponent

end

end OAI
