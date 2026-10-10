import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.OriginCoordinates

namespace OAI

/-! Fraction charts, global lattices and finite origin quotients. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
variable (k : Type*) [Field k]
abbrev planeFractionField := FractionRing (MvPolynomial (Fin 2) k)

noncomputable instance planeCoordinateRing_gcd : GCDMonoid (MvPolynomial (Fin 2) k) :=
  UniqueFactorizationMonoid.toGCDMonoid _

lemma planeCoordinates_relPrime :
    IsRelPrime (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) := by
  apply (MvPolynomial.X_prime (R := k) (i := (0 : Fin 2))).irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_dvd_X.mp h)

lemma planeFractionCoordinate_ne_zero (i : Fin 2) :
    algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) (MvPolynomial.X i) ≠ 0 :=
  fun h => MvPolynomial.X_ne_zero i
    ((FaithfulSMul.algebraMap_injective _ _) (h.trans (map_zero _).symm))

noncomputable def planeChartToFraction (i : Fin 2) :
    planeCoordinateChart k i →ₐ[k] planeFractionField k :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X i : MvPolynomial (Fin 2) k)
    (f := IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (planeFractionField k))
    (isUnit_iff_ne_zero.mpr (planeFractionCoordinate_ne_zero k i))

lemma planeChartToFraction_algebraMap (i : Fin 2) (P : MvPolynomial (Fin 2) k) :
    planeChartToFraction k i
      (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i) P) =
      algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) P :=
  IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr (planeFractionCoordinate_ne_zero k i)) _

lemma planeChartToFraction_injective (i : Fin 2) :
    Function.Injective (planeChartToFraction k i) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
    (planeChartToFraction k i).toRingHom).mpr
  intro P Q
  constructor
  · exact congrArg (planeChartToFraction k i)
  · intro h
    have h' : algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) P =
        algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) Q := by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, planeChartToFraction_algebraMap] using h
    exact congrArg (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i))
      ((FaithfulSMul.algebraMap_injective _ _) h')

noncomputable def planeChartToFractionLinear (i : Fin 2) :
    planeCoordinateChart k i →ₗ[MvPolynomial (Fin 2) k] planeFractionField k where
  toFun := planeChartToFraction k i
  map_add' := (planeChartToFraction k i).map_add
  map_smul' := by
    intro P f
    simp only [Algebra.smul_def, map_mul, planeChartToFraction_algebraMap,
      RingHom.id_apply]

noncomputable def planeOverlapToFraction : planeOverlapRing k →ₐ[k] planeFractionField k :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
    (f := IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (planeFractionField k))
    (isUnit_iff_ne_zero.mpr (by
      change algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
        (MvPolynomial.X 0 * MvPolynomial.X 1) ≠ 0
      rw [map_mul]
      exact mul_ne_zero (planeFractionCoordinate_ne_zero k 0) (planeFractionCoordinate_ne_zero k 1)))

lemma planeOverlapToFraction_algebraMap (P : MvPolynomial (Fin 2) k) :
    planeOverlapToFraction k
      (algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k) P) =
      algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) P := by
  unfold planeOverlapToFraction
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

lemma planeChartToFraction_overlap (i : Fin 2) (f : planeCoordinateChart k i) :
    planeOverlapToFraction k (planeChartToOverlap k i f) = planeChartToFraction k i f := by
  have h : (planeOverlapToFraction k).toRingHom.comp (planeChartToOverlap k i).toRingHom =
      (planeChartToFraction k i).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      planeChartToOverlap_algebraMap, planeChartToFraction_algebraMap,
      planeOverlapToFraction_algebraMap]
  exact RingHom.congr_fun h f

noncomputable def planeOverlapInverse : planeOverlapRing k :=
  IsLocalization.Away.invSelf (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)

lemma planeOverlapInverse_evaluation (x : planeTorusPoints k) :
    planeOverlapEvaluation k (planeOverlapInverse k) x = (x.val 0 * x.val 1)⁻¹ := by
  have h := congrFun (congrArg (planeOverlapEvaluation k)
    (IsLocalization.Away.mul_invSelf (S := planeOverlapRing k)
      (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k))) x
  simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply,
    planeOverlapEvaluation_algebraMap, planeTorusEvaluation_apply,
    MvPolynomial.eval_X] at h
  exact mul_left_cancel₀ (mul_ne_zero (x.property 0) (x.property 1))
    (h.trans (mul_inv_cancel₀ (mul_ne_zero (x.property 0) (x.property 1))).symm)

lemma planeOverlapInverse_fraction :
    planeOverlapToFraction k (planeOverlapInverse k) =
      (algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
        (MvPolynomial.X 0 * MvPolynomial.X 1))⁻¹ := by
  have h := congrArg (planeOverlapToFraction k)
    (IsLocalization.Away.mul_invSelf (S := planeOverlapRing k)
      (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k))
  simp only [map_mul, map_one, planeOverlapToFraction_algebraMap] at h
  have hn : algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
      (MvPolynomial.X 0 * MvPolynomial.X 1) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero (planeFractionCoordinate_ne_zero k 0) (planeFractionCoordinate_ne_zero k 1)
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  simpa only [map_mul, planeOverlapInverse] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma planeChartVector_mem (a : Fin 2) (f : ι → planeCoordinateChart k a) :
    (fun i => planeChartToFraction k a (f i)) ∈
      powerLocalization (MvPolynomial.X a : MvPolynomial (Fin 2) k) coordinateLattice := by
  obtain ⟨s,hs⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers (MvPolynomial.X a : MvPolynomial (Fin 2) k)) Finset.univ f
  obtain ⟨n,hn⟩ := s.property
  refine ⟨n, (mem_coordinateLattice _).mpr fun i => ?_⟩
  obtain ⟨b,hb⟩ := hs i (Finset.mem_univ i)
  refine ⟨b,?_⟩
  have h := congrArg (planeChartToFraction k a) hb
  rw [planeChartToFraction_algebraMap] at h
  change _ = planeChartToFraction k a (s.val • f i) at h
  rw [← hn] at h
  exact h.trans ((planeChartToFractionLinear k a).map_smul (MvPolynomial.X a ^ n) (f i))

variable [Infinite k]
variable (P : Matrix ι ι (Polynomial k))

omit [DecidableEq ι] in
lemma planeChartPair_fraction_relation
    (f₀ : ι → planeCoordinateChart k 0) (f₁ : ι → planeCoordinateChart k 1)
    (hf : ∀ x : planeTorusPoints k,
      (fun j => planeChartEvaluation k 1 (f₁ j) x) =
        (polynomialMatrixEval P ((x.val 0 * x.val 1)⁻¹)).mulVec
          (fun j => planeChartEvaluation k 0 (f₀ j) x)) :
    (fun i => planeChartToFraction k 1 (f₁ i)) =
      (polynomialMatrixEval P ((algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
        (MvPolynomial.X 0 * MvPolynomial.X 1))⁻¹)).mulVec
          (fun i => planeChartToFraction k 0 (f₀ i)) := by
  have hov (i : ι) : planeChartToOverlap k 1 (f₁ i) =
      ∑ j, Polynomial.aeval (planeOverlapInverse k) (P i j) * planeChartToOverlap k 0 (f₀ j) := by
    apply planeOverlapEvaluation_injective k
    funext x
    let ev : planeOverlapRing k →ₐ[k] k :=
      (Pi.evalAlgHom k _ x).comp (planeOverlapEvaluation k)
    change ev (planeChartToOverlap k 1 (f₁ i)) = ev _
    simp only [map_sum, map_mul, map_aeval_polynomial]
    change planeOverlapEvaluation k (planeChartToOverlap k 1 (f₁ i)) x =
      ∑ j, Polynomial.aeval (planeOverlapEvaluation k (planeOverlapInverse k) x) (P i j) *
        planeOverlapEvaluation k (planeChartToOverlap k 0 (f₀ j)) x
    simp only [planeChartToOverlap_evaluation, planeOverlapInverse_evaluation]
    exact congrFun (hf x) i
  funext i
  have h := congrArg (planeOverlapToFraction k) (hov i)
  simpa only [map_sum, map_mul, map_aeval_polynomial, planeChartToFraction_overlap,
    planeOverlapInverse_fraction, Matrix.mulVec, dotProduct, polynomialMatrixEval] using h

variable (h0 : polynomialMatrixEval P (0 : k) = 1)
    (hadd : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)

noncomputable def planeGlobalTransition :
    (ι → planeFractionField k) ≃ₗ[planeFractionField k] (ι → planeFractionField k) :=
  polynomialActionEquiv P h0 hadd
    (-(algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
      (MvPolynomial.X 0 * MvPolynomial.X 1))⁻¹)

noncomputable def planeGlobalLattice :
    Submodule (MvPolynomial (Fin 2) k) (ι → planeFractionField k) :=
  gluedLattice (MvPolynomial.X 0) (MvPolynomial.X 1) (planeGlobalTransition k P h0 hadd)

omit [Infinite k] in
lemma planeFraction_product_ne_zero :
    algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
      (MvPolynomial.X 0 * MvPolynomial.X 1) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero (planeFractionCoordinate_ne_zero k 0) (planeFractionCoordinate_ne_zero k 1)

lemma planeGlobalTransition_denominator (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    ∀ v ∈ coordinateLattice (R := MvPolynomial (Fin 2) k),
      (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)^d •
        planeGlobalTransition k P h0 hadd v ∈ coordinateLattice (R := MvPolynomial (Fin 2) k) :=
  polynomialAction_denominator P h0 hadd _ (planeFraction_product_ne_zero k) d hd

lemma planeGlobalLattice_finite (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    Module.Finite (MvPolynomial (Fin 2) k) (planeGlobalLattice k P h0 hadd) :=
  gluedLattice_finite _ _ (MvPolynomial.X_ne_zero 0) (planeCoordinates_relPrime k) _ d
    (planeGlobalTransition_denominator k P h0 hadd d hd)

lemma planeChartPair_mem_globalLattice
    (f₀ : ι → planeCoordinateChart k 0) (f₁ : ι → planeCoordinateChart k 1)
    (hf : ∀ x : planeTorusPoints k,
      (fun j => planeChartEvaluation k 1 (f₁ j) x) =
        (polynomialMatrixEval P ((x.val 0 * x.val 1)⁻¹)).mulVec
          (fun j => planeChartEvaluation k 0 (f₀ j) x)) :
    (fun i => planeChartToFraction k 0 (f₀ i)) ∈ planeGlobalLattice k P h0 hadd := by
  constructor
  · exact planeChartVector_mem k 0 f₀
  · refine ⟨fun i => planeChartToFraction k 1 (f₁ i), planeChartVector_mem k 1 f₁, ?_⟩
    have h := planeChartPair_fraction_relation k P f₀ f₁ hf
    change planeGlobalTransition k P h0 hadd (fun i => planeChartToFraction k 1 (f₁ i)) = _
    rw [h]
    change (polynomialMatrixEval P (-_)).mulVec ((polynomialMatrixEval P _).mulVec _) = _
    rw [Matrix.mulVec_mulVec, ← polynomialMatrixEval_add P hadd, neg_add_cancel,
      polynomialMatrixEval_zero P h0, Matrix.one_mulVec]

end

section
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))

omit [Infinite k] in
include hP in
lemma associatedPolynomial_zero : polynomialMatrixEval P (0 : k) = 1 := by
  rw [hP]
  change LinearMap.toMatrix' (ρ 1) = 1
  rw [map_one]
  exact LinearMap.toMatrix'_one

omit [Infinite k] in
include hP in
lemma associatedPolynomial_add (s t : k) : polynomialMatrixEval P (s+t) =
    polynomialMatrixEval P s * polynomialMatrixEval P t := by
  rw [hP, hP, hP]
  change LinearMap.toMatrix' (ρ (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) = _
  rw [map_mul, LinearMap.toMatrix'_mul]

noncomputable def associatedFractionChart :
    (associatedSectionsSubmodule k ι ρ) →ₗ[MvPolynomial (Fin 2) k]
      (ι → planeFractionField k) :=
  (LinearMap.pi fun i => (planeChartToFractionLinear k 0).comp
    (LinearMap.proj i)).comp (associatedXChartPolynomial k ι ρ)

omit [Fintype ι] [DecidableEq ι] in
lemma associatedFractionChart_injective : Function.Injective (associatedFractionChart k ι ρ) := by
  intro f g h
  apply associatedXChart_injective k ι ρ
  funext i
  exact planeChartToFraction_injective k 0 (congrFun h i)

lemma associatedFractionChart_mem (f : associatedSectionsSubmodule k ι ρ) :
    associatedFractionChart k ι ρ f ∈ planeGlobalLattice k P
      (associatedPolynomial_zero k ι ρ P hP) (associatedPolynomial_add k ι ρ P hP) := by
  apply planeChartPair_mem_globalLattice k P _ _
    (associatedXChart k ι ρ f) (associatedYChart k ι ρ f)
  intro x
  rw [hP, LinearMap.toMatrix'_mulVec]
  exact associatedCharts_transition k ι ρ f x

include hP in
 

theorem associatedSections_finite (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    Module.Finite (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) := by
  let L := planeGlobalLattice k P
    (associatedPolynomial_zero k ι ρ P hP) (associatedPolynomial_add k ι ρ P hP)
  let : Module.Finite (MvPolynomial (Fin 2) k) L :=
    planeGlobalLattice_finite k P _ _ d hd
  let f := (associatedFractionChart k ι ρ).codRestrict L
    (associatedFractionChart_mem k ι ρ P hP)
  exact Module.Finite.of_injective f fun a b h =>
    associatedFractionChart_injective k ι ρ (congrArg Subtype.val h)

end

variable {k M σ : Type*} [Field k] [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

lemma originQuotient_polynomial_smul (N : Submodule k M)
    (hX : ∀ (i : σ) (m : M), (MvPolynomial.X i : MvPolynomial σ k) • m ∈ N)
    (P : MvPolynomial σ k) (m : M) :
    N.mkQ (P • m) = MvPolynomial.constantCoeff P • N.mkQ m := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.constantCoeff_C]
    change N.mkQ (algebraMap k (MvPolynomial σ k) a • m) = a • N.mkQ m
    rw [algebraMap_smul, map_smul]
  | add P Q hP hQ => simp only [add_smul, map_add, hP, hQ]
  | mul_X P i _ =>
    rw [mul_comm, mul_smul]
    have hz : N.mkQ ((MvPolynomial.X i : MvPolynomial σ k) • (P • m)) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (hX i (P • m))
    simpa using hz

 

theorem originQuotient_finite (N : Submodule k M)
    (hX : ∀ (i : σ) (m : M), (MvPolynomial.X i : MvPolynomial σ k) • m ∈ N)
    [Module.Finite (MvPolynomial σ k) M] : Module.Finite k (M ⧸ N) := by
  let f : M →ₛₗ[MvPolynomial.constantCoeff] (M ⧸ N) :=
    { toFun := N.mkQ
      map_add' := N.mkQ.map_add
      map_smul' := originQuotient_polynomial_smul N hX }
  exact Module.Finite.of_surjective f N.mkQ_surjective

end FiberFunctorProof
end

end OAI
