import Mathlib.LinearAlgebra.StdBasis
import OAI.AlgebraicGeometry.PlaneCurves.LaurentCoefficients

namespace OAI

/-!
# Coefficient, residue-class, and degree-zero bases of section spaces
-/

section

/-! Generic finite-coefficient basis assembly for Section 2.
The coefficient map and its injectivity remain explicit inputs. Surjectivity
is proved from actual vectors having the coordinate delta values; no dimension
or unexplained basis assumption is introduced. -/
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10

variable {R V I : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  [Fintype I] [DecidableEq I]

/-- Delta-valued coefficient vectors give every finite coefficient array. -/
theorem coefficientMap_surjective (c : V →ₗ[R] (I → R)) (v : I → V)
    (hv : ∀ i, c (v i) = Pi.single i 1) : Function.Surjective c := by
  intro a
  refine ⟨∑ i, a i • v i, ?_⟩
  ext j
  simp [map_sum, hv, Pi.single_apply]

/-- Injectivity and checked delta coefficient values produce a linear equivalence. -/
def coefficientEquiv (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : V ≃ₗ[R] (I → R) :=
  LinearEquiv.ofBijective c ⟨hc, coefficientMap_surjective c v hv⟩

/-- The basis is constructed from the proved equivalence, not supplied as data. -/
def basisFromCoefficients (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : Basis I R V :=
  (Pi.basisFun R I).map (coefficientEquiv c hc v hv).symm

/-- Its actual vectors are exactly the specified coefficient-delta vectors. -/
@[simp] theorem basisFromCoefficients_apply
    (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) (i : I) :
    basisFromCoefficients c hc v hv i = v i := by
  apply (coefficientEquiv c hc v hv).injective
  change coefficientEquiv c hc v hv
    ((coefficientEquiv c hc v hv).symm (Pi.basisFun R I i)) = c (v i)
  rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, hv]

/-- Coordinate extraction computes the basis representation exactly. -/
theorem basisFromCoefficients_repr
    (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) (x : V) (i : I) :
    (basisFromCoefficients c hc v hv).repr x i = c x i := by
  change (Pi.basisFun R I).repr (c x) i = c x i
  exact Pi.basisFun_repr R I (c x) i

/-- Every vector is the finite sum of its actual extracted coefficients. -/
theorem coefficient_reconstruction
    (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) (x : V) :
    ∑ i, c x i • v i = x := by
  apply hc
  ext j
  simp [map_sum, hv, Pi.single_apply]

end Nagata.Workers.W10

end
end

section

/-! Genuine constant sections and the degree-zero coefficient block.
Its exhaustion proof is conditional only on actual Laurent injectivity,
automorphy recurrence, and the constant-section coefficient computation. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08

/-- A genuine constant section on C*, represented by zero extension at zero. -/
def normalizedConstantSection (τ : ℂ) (hτ : τ ≠ 0) (a : ℂ) :
    automorphicSections τ 0 1 :=
  sectionOfFunction hτ (fun _ => a) (fun _ _ => differentiableAt_const a)
    (by intro z hz; simp)

@[simp] theorem normalizedConstantSection_apply (τ : ℂ) (hτ : τ ≠ 0) (a : ℂ)
    {z : ℂ} (hz : z ≠ 0) : (normalizedConstantSection τ hτ a).val z = a :=
  sectionOfFunction_apply hτ _ _ _ hz

/-- The coefficient at zero is the unique finite coordinate of the constant tip. -/
def zeroCoefficientMap {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) : V →ₗ[ℂ] (PUnit → ℂ) where
  toFun f _ := C f 0
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

/-- Degree-zero automorphy forces every nonzero-index coefficient to vanish. -/
theorem zeroDegree_coeff_eq_zero {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) {τ : ℂ} (hτnorm : ‖τ‖ < 1)
    (hrec : ∀ f k, C f k = τ ^ k * C f k) (f : V) {k : ℤ} (hk : k ≠ 0) :
    C f k = 0 := by
  have hfactor : τ ^ k - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hk (period_zpow_eq_one hτnorm he)
  have hprod : (τ ^ k - 1) * C f k = 0 := by
    rw [sub_mul, one_mul, ← hrec f k, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left hfactor

/-- All Laurent coefficients reduce to the one zero-index coordinate. -/
theorem zeroCoefficientMap_injective {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    {τ : ℂ} (hτnorm : ‖τ‖ < 1)
    (hrec : ∀ f k, C f k = τ ^ k * C f k) :
    Function.Injective (zeroCoefficientMap C) := by
  intro f g hfg
  apply hC
  ext k
  by_cases hk : k = 0
  · subst k
    exact congrFun hfg PUnit.unit
  · rw [zeroDegree_coeff_eq_zero C hτnorm hrec f hk,
      zeroDegree_coeff_eq_zero C hτnorm hrec g hk]

/-- The actual normalized constant section is the degree-zero basis vector,
once its actual coefficient and analytic Laurent uniqueness are established. -/
def zeroDegreeBasisOfLaurentData (τ : ℂ) (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1)
    (C : automorphicSections τ 0 1 →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (hrec : ∀ f k, C f k = τ ^ k * C f k)
    (hconstant : C (normalizedConstantSection τ hτ 1) 0 = 1) :
    Basis PUnit ℂ (automorphicSections τ 0 1) := by
  apply basisFromCoefficients (zeroCoefficientMap C)
    (zeroCoefficientMap_injective C hC hτnorm hrec)
    (fun _ => normalizedConstantSection τ hτ 1)
  intro i
  ext j
  simpa [zeroCoefficientMap, Pi.single_apply] using hconstant

@[simp] theorem zeroDegreeBasisOfLaurentData_apply
    (τ : ℂ) (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1)
    (C : automorphicSections τ 0 1 →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (hrec : ∀ f k, C f k = τ ^ k * C f k)
    (hconstant : C (normalizedConstantSection τ hτ 1) 0 = 1) (i : PUnit) :
    zeroDegreeBasisOfLaurentData τ hτ hτnorm C hC hrec hconstant i =
      normalizedConstantSection τ hτ 1 := by
  exact basisFromCoefficients_apply _ _ _ _ i

end Nagata.Workers.W10

end
end

section

noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09

/-- Restrict an actual coefficient map to the manuscript's finite residue interval. -/
def residueCoefficientMap {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ) :
    V →ₗ[ℂ] (thetaIndices U n → ℂ) where
  toFun f K := C f K.val
  map_add' f g := by ext K; simp
  map_smul' a f := by ext K; simp

/-- Recurrence determination turns analytic uniqueness of all Laurent coefficients
into injectivity of the finitely many residue coefficients. -/
theorem residueCoefficientMap_injective {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (τ γ : ℂ) (hτ : τ ≠ 0) (hγ : γ ≠ 0) (U : ℝ) {n : ℤ} (hn : 0 < n)
    (hrec : ∀ f k, C f (k + n) = γ⁻¹ * τ ^ k * C f k) :
    Function.Injective (residueCoefficientMap C U n) := by
  intro f g h
  apply hC
  apply laurent_recurrence_eq_of_thetaIndices τ γ hτ hγ U hn
    (C f) (C g) (hrec f) (hrec g)
  intro K hK
  exact congrFun h ⟨K, hK⟩

/-- A basis of the actual section space follows once actual Laurent uniqueness,
recurrence, and the theta coefficient identities have been proved. -/
def sectionBasisOfLaurentData (τ γ : ℂ) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (U : ℝ) (n : ℤ) (hn : 0 < n)
    (C : automorphicSections τ n γ →ₗ[ℂ] (ℤ → ℂ))
    (hC : Function.Injective C)
    (hrec : ∀ f k, C f (k + n) = γ⁻¹ * τ ^ k * C f k)
    (theta : thetaIndices U n → automorphicSections τ n γ)
    (htheta : ∀ K, residueCoefficientMap C U n (theta K) = Pi.single K 1) :
    Basis (thetaIndices U n) ℂ (automorphicSections τ n γ) := by
  classical
  exact basisFromCoefficients (residueCoefficientMap C U n)
    (residueCoefficientMap_injective C hC τ γ hτ hγ U hn hrec) theta htheta

@[simp] theorem sectionBasisOfLaurentData_apply
    (τ γ : ℂ) (hτ : τ ≠ 0) (hγ : γ ≠ 0) (U : ℝ) (n : ℤ) (hn : 0 < n)
    (C : automorphicSections τ n γ →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (hrec : ∀ f k, C f (k + n) = γ⁻¹ * τ ^ k * C f k)
    (theta : thetaIndices U n → automorphicSections τ n γ)
    (htheta : ∀ K, residueCoefficientMap C U n (theta K) = Pi.single K 1)
    (K : thetaIndices U n) :
    sectionBasisOfLaurentData τ γ hτ hγ U n hn C hC hrec theta htheta K = theta K := by
  classical
  exact basisFromCoefficients_apply _ _ _ _ K

end Nagata.Workers.W10

end
end

section

/-! Nonzero diagonal normalization for actual centered theta coefficients. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W09

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

/-- Divide each actual residue coefficient by its nonzero normalization scalar. -/
def normalizedResidueMap (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ)
    (a : thetaIndices U n → ℂ) : V →ₗ[ℂ] (thetaIndices U n → ℂ) where
  toFun f K := (a K)⁻¹ * C f K.val
  map_add' f g := by ext K; simp [mul_add]
  map_smul' b f := by ext K; simp [mul_left_comm]

theorem normalizedResidueMap_injective (C : V →ₗ[ℂ] (ℤ → ℂ))
    (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n)) :
    Function.Injective (normalizedResidueMap C U n a) := by
  intro f g h
  apply hc
  ext K
  have he := congrFun h K
  change (a K)⁻¹ * C f K.val = (a K)⁻¹ * C g K.val at he
  exact mul_left_cancel₀ (inv_ne_zero (ha K)) he

/-- Orbit support and the diagonal coefficient imply the full finite delta
identity, since the chosen indices have distinct residues. -/
theorem normalizedResidueMap_delta (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0) (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k)
    (K : thetaIndices U n) :
    normalizedResidueMap C U n a (theta K) = Pi.single K 1 := by
  classical
  ext L
  change (a L)⁻¹ * C (theta K) L.val = _
  rw [hcoeff]
  by_cases hLK : L = K
  · subst L
    simp [supportedOrbitCoefficient_initial, ha]
  · have hz : supportedOrbitCoefficient τ γ n K.val (a K) L.val = 0 := by
      by_contra hne
      have he := thetaIndices_residue_injective L.property K.property
        (supportedOrbitCoefficient_residue τ γ n K.val (a K) L.val hne)
      exact hLK (Subtype.ext he)
    simp [hz, hLK]

/-- The actual centered vectors themselves form a basis. No rescaling of the
vectors is needed; normalization occurs only in coefficient extraction. -/
def basisFromSupportedOrbits (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n))
    (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k) :
    Basis (thetaIndices U n) ℂ V :=
  basisFromCoefficients (normalizedResidueMap C U n a)
    (normalizedResidueMap_injective C U n a ha hc) theta
    (normalizedResidueMap_delta C τ γ U n a ha theta hcoeff)

@[simp] theorem basisFromSupportedOrbits_apply (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n))
    (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k)
    (K : thetaIndices U n) : basisFromSupportedOrbits C τ γ U n a ha hc theta hcoeff K = theta K :=
  basisFromCoefficients_apply _ _ _ _ K

end Nagata.Workers.W10

end
end

end OAI
