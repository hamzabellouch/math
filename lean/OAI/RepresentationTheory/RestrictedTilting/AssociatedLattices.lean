import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.GlobalLattices

namespace OAI

/-! Associated-origin finiteness, lattice equivalence and numerator evaluations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma associatedCoordinate_smul (i : Fin 2) (f : associatedSectionsSubmodule k ι ρ) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) • f = associatedCoordinateMul k ι ρ i f := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  funext g
  change ((MvPolynomial.X i : MvPolynomial (Fin 2) k) • f.val j).val g =
    (regularFirstColumn k i).val g * (f.val j).val g
  rw [Algebra.smul_def, regularPlane_algebraMap]
  change (regularPlane k (MvPolynomial.X i)).val g * (f.val j).val g = _
  rw [regularPlane_evaluation, MvPolynomial.eval_X, regularFirstColumn_apply]

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma associatedOrigin_coordinate_mem (i : Fin 2) (f : associatedSectionsSubmodule k ι ρ) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) • f ∈ associatedOriginRelations k ι ρ := by
  rw [associatedCoordinate_smul]
  fin_cases i
  · exact Submodule.mem_sup_left ⟨f,rfl⟩
  · exact Submodule.mem_sup_right ⟨f,rfl⟩

 

theorem associatedOrigin_finite
    (P : Matrix ι ι (Polynomial k))
    (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
    (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    Module.Finite k (associatedOriginRep k ι ρ).V := by
  let : Module.Finite (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) :=
    associatedSections_finite k ι ρ P hP d hd
  exact originQuotient_finite (associatedOriginRelations k ι ρ)
    (associatedOrigin_coordinate_mem k ι ρ)

end

section
variable (k : Type*) [Field k]

lemma planeChartToFraction_invSelf (a : Fin 2) :
    planeChartToFraction k a
      (IsLocalization.Away.invSelf (MvPolynomial.X a : MvPolynomial (Fin 2) k)) =
      (algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) (MvPolynomial.X a))⁻¹ := by
  have h := congrArg (planeChartToFraction k a)
    (IsLocalization.Away.mul_invSelf (S := planeCoordinateChart k a)
      (MvPolynomial.X a : MvPolynomial (Fin 2) k))
  rw [map_mul, map_one, planeChartToFraction_algebraMap] at h
  apply mul_left_cancel₀ (planeFractionCoordinate_ne_zero k a)
  rw [mul_inv_cancel₀ (planeFractionCoordinate_ne_zero k a)]
  exact h

lemma planeChartVector_exists {ι : Type*} (a : Fin 2) (v : ι → planeFractionField k)
    (hv : v ∈ powerLocalization (MvPolynomial.X a : MvPolynomial (Fin 2) k) coordinateLattice) :
    ∃ f : ι → planeCoordinateChart k a, (fun i => planeChartToFraction k a (f i)) = v := by
  obtain ⟨n,hn⟩ := hv
  choose b hb using (mem_coordinateLattice _).mp hn
  refine ⟨fun i => algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k a) (b i) *
    IsLocalization.Away.invSelf (MvPolynomial.X a : MvPolynomial (Fin 2) k)^n, ?_⟩
  funext i
  rw [map_mul, map_pow, planeChartToFraction_algebraMap, planeChartToFraction_invSelf, hb]
  change ((MvPolynomial.X a : MvPolynomial (Fin 2) k)^n • v i) * _ = _
  rw [Algebra.smul_def, map_pow]
  rw [inv_pow, mul_assoc, mul_comm (v i), ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n (planeFractionCoordinate_ne_zero k a)), one_mul]

lemma planeOverlapToFraction_injective : Function.Injective (planeOverlapToFraction k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k))
    (planeOverlapToFraction k).toRingHom).mpr
  intro P Q
  constructor
  · exact congrArg (planeOverlapToFraction k)
  · intro h
    have h' : algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) P =
        algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k) Q := by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        planeOverlapToFraction_algebraMap] using h
    exact congrArg (algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k))
      ((FaithfulSMul.algebraMap_injective _ _) h')

variable {ι : Type*} [Fintype ι]
lemma planeChartPair_evaluation_relation (P : Matrix ι ι (Polynomial k))
    (f₀ : ι → planeCoordinateChart k 0) (f₁ : ι → planeCoordinateChart k 1)
    (hf : (fun i => planeChartToFraction k 1 (f₁ i)) =
      (polynomialMatrixEval P ((algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
        (MvPolynomial.X 0 * MvPolynomial.X 1))⁻¹)).mulVec
          (fun i => planeChartToFraction k 0 (f₀ i))) (x : planeTorusPoints k) :
    (fun i => planeChartEvaluation k 1 (f₁ i) x) =
      (polynomialMatrixEval P ((x.val 0 * x.val 1)⁻¹)).mulVec
        (fun i => planeChartEvaluation k 0 (f₀ i) x) := by
  have hov (i : ι) : planeChartToOverlap k 1 (f₁ i) =
      ∑ j, Polynomial.aeval (planeOverlapInverse k) (P i j) * planeChartToOverlap k 0 (f₀ j) := by
    apply planeOverlapToFraction_injective k
    simp only [map_sum, map_mul, map_aeval_polynomial, planeChartToFraction_overlap,
      planeOverlapInverse_fraction]
    simpa only [polynomialMatrixEval, Matrix.mulVec, dotProduct, map_mul] using congrFun hf i
  funext i
  let ev : planeOverlapRing k →ₐ[k] k :=
    (Pi.evalAlgHom k _ x).comp (planeOverlapEvaluation k)
  have h := congrArg ev (hov i)
  simp only [map_sum, map_mul, map_aeval_polynomial] at h
  change planeOverlapEvaluation k (planeChartToOverlap k 1 (f₁ i)) x =
    ∑ j, Polynomial.aeval (planeOverlapEvaluation k (planeOverlapInverse k) x) (P i j) *
      planeOverlapEvaluation k (planeChartToOverlap k 0 (f₀ j)) x at h
  simpa only [planeChartToOverlap_evaluation, planeOverlapInverse_evaluation,
    polynomialMatrixEval, Matrix.mulVec, dotProduct] using h

end

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))

noncomputable def associatedLatticeMap :
    (associatedSectionsSubmodule k ι ρ) →ₗ[MvPolynomial (Fin 2) k]
      planeGlobalLattice k P (associatedPolynomial_zero k ι ρ P hP)
        (associatedPolynomial_add k ι ρ P hP) :=
  (associatedFractionChart k ι ρ).codRestrict _ (associatedFractionChart_mem k ι ρ P hP)

lemma associatedLatticeMap_surjective : Function.Surjective (associatedLatticeMap k ι ρ P hP) := by
  intro v
  obtain ⟨f₀,h₀⟩ := planeChartVector_exists k 0 v.val v.property.1
  obtain ⟨w,hw,he⟩ := v.property.2
  obtain ⟨f₁,h₁⟩ := planeChartVector_exists k 1 w hw
  have hrel : (fun i => planeChartToFraction k 1 (f₁ i)) =
      (polynomialMatrixEval P ((algebraMap (MvPolynomial (Fin 2) k) (planeFractionField k)
        (MvPolynomial.X 0 * MvPolynomial.X 1))⁻¹)).mulVec
          (fun i => planeChartToFraction k 0 (f₀ i)) := by
    rw [h₀, h₁]
    change planeGlobalTransition k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP) w = v.val at he
    have h := congrArg (planeGlobalTransition k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP)).symm he
    rw [LinearEquiv.symm_apply_apply] at h
    rw [planeGlobalTransition, polynomialActionEquiv_symm, neg_neg] at h
    simpa only [polynomialActionEquiv, LinearEquiv.coe_mk, Matrix.toLin'_apply] using h
  have htrans (x : planeTorusPoints k) :
      (fun i => planeChartEvaluation k 1 (f₁ i) x) =
        ρ (Multiplicative.ofAdd ((x.val 0*x.val 1)⁻¹))
          (fun i => planeChartEvaluation k 0 (f₀ i) x) := by
    have h := planeChartPair_evaluation_relation k P f₀ f₁ hrel x
    rwa [hP, LinearMap.toMatrix'_mulVec] at h
  obtain ⟨f,hf,_⟩ := associatedChartPair_glue k ι ρ P hP f₀ f₁ htrans
  refine ⟨f, Subtype.ext ?_⟩
  change (fun i => planeChartToFraction k 0 (associatedXChart k ι ρ f i)) = v.val
  rw [hf]
  exact h₀

 

noncomputable def associatedLatticeEquiv :
    (associatedSectionsSubmodule k ι ρ) ≃ₗ[MvPolynomial (Fin 2) k]
      planeGlobalLattice k P (associatedPolynomial_zero k ι ρ P hP)
        (associatedPolynomial_add k ι ρ P hP) :=
  LinearEquiv.ofBijective (associatedLatticeMap k ι ρ P hP)
    ⟨fun _ _ h => associatedFractionChart_injective k ι ρ (congrArg Subtype.val h),
      associatedLatticeMap_surjective k ι ρ P hP⟩


omit [Fintype ι] [DecidableEq ι] in
lemma associatedFractionChart_apply (f : associatedSectionsSubmodule k ι ρ) (i : ι) :
    associatedFractionChart k ι ρ f i =
      planeChartToFraction k 0 (associatedXChart k ι ρ f i) := rfl

include hP in
lemma associatedNumerator_exists (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
    (f : associatedSectionsSubmodule k ι ρ) :
    ∃ F : ι → MvPolynomial (Fin 2) k, ∀ i,
      algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k 0) (F i) =
        planeChartCoordinate k 0 0 ^ d * associatedXChart k ι ρ f i := by
  have hb := gluedLattice_bound (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)
    (MvPolynomial.X 1) (MvPolynomial.X_ne_zero 0) (planeCoordinates_relPrime k)
    (planeGlobalTransition k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP)) d
    (planeGlobalTransition_denominator k P (associatedPolynomial_zero k ι ρ P hP)
      (associatedPolynomial_add k ι ρ P hP) d hd)
    (associatedFractionChart_mem k ι ρ P hP f)
  choose F hF using (mem_coordinateLattice _).mp hb
  refine ⟨F, fun i => planeChartToFraction_injective k 0 ?_⟩
  rw [planeChartToFraction_algebraMap, map_mul, map_pow,
    planeChartCoordinate, planeChartToFraction_algebraMap]
  simpa only [Pi.smul_apply, Algebra.smul_def, map_pow, associatedFractionChart_apply] using hF i

omit [Fintype ι] [DecidableEq ι] in
lemma associatedNumerator_evaluation (d : ℕ) (f : associatedSectionsSubmodule k ι ρ)
    (F : ι → MvPolynomial (Fin 2) k)
    (hF : ∀ i, algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k 0) (F i) =
      planeChartCoordinate k 0 0 ^ d * associatedXChart k ι ρ f i)
    (x : planeTorusPoints k) (i : ι) :
    MvPolynomial.eval x.val (F i) =
      (x.val 0)^d * planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x := by
  have h := congrFun (congrArg (planeChartEvaluation k 0) (hF i)) x
  simpa only [planeChartEvaluation_algebraMap, planeTorusEvaluation_apply,
    map_mul, map_pow, Pi.mul_apply, Pi.pow_apply, planeChartEvaluation_coordinate] using h

end FiberFunctorProof
end

end OAI
