import OAI.AlgebraicGeometry.SurfaceCones.SectionFiniteChart

namespace OAI


/-! Injectivity for the actual line-bundle polynomial presentation, derived
from transcendence over the actual coefficient-ring image. -/
noncomputable section
namespace Polynomial
open scoped _root_.Polynomial
variable {k R F : Type*} [CommRing k] [CommRing R] [CommRing F]
    [Algebra k R] [Algebra k F]

lemma eval₂RingHom_injective_of_range_transcendental (f : R →ₐ[k] F)
    (hf : Function.Injective f) (x : F) (hx : Transcendental f.range x) :
    Function.Injective (_root_.Polynomial.eval₂RingHom f.toRingHom x) := by
  let e := AlgEquiv.ofInjective f hf
  have he : _root_.Polynomial.eval₂RingHom f.toRingHom x =
      (_root_.Polynomial.aeval (R := f.range) x).toRingHom.comp (_root_.Polynomial.mapRingHom e.toRingHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      change _root_.Polynomial.eval₂ f.toRingHom x (_root_.Polynomial.C a) =
        _root_.Polynomial.aeval (R := f.range) x (Polynomial.map e.toRingHom (_root_.Polynomial.C a))
      rw [_root_.Polynomial.eval₂_C, _root_.Polynomial.map_C, _root_.Polynomial.aeval_C]
      rfl
    · simp
  rw [he]
  exact (transcendental_iff_injective.mp hx).comp (_root_.Polynomial.map_injective e.toRingHom e.injective)

end Polynomial


/-! Independence of the radial coordinate from the actual projective-chart
coefficient ring. This is needed for the faithful line-bundle chart of W. -/
open _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization _root_.MvPolynomial _root_.OAI.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance fieldRing : Ring K := (inferInstance : CommRing K).toRing

/-- Affine blowup coordinates inside the original rational function field. -/
def blowupCoordinate (i j : Fin 3) : K :=
  if j = i then coordinate i else coordinate j / coordinate i

lemma blowupCoordinate_independent (i : Fin 3) :
    AlgebraicIndependent ℂ (blowupCoordinate i) := by
  have hc : AlgebraicIndependent ℂ coordinate :=
    (algebraicIndependent_X (Fin 3) ℂ).map
      (f := IsScalarTower.toAlgHom ℂ S K) (IsFractionRing.injective S K).injOn
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions hc
  intro j
  have hi : blowupCoordinate i i ∈ Algebra.adjoin ℂ (Set.range (blowupCoordinate i)) :=
    Algebra.subset_adjoin (Set.mem_range_self i)
  have hj : blowupCoordinate i j ∈ Algebra.adjoin ℂ (Set.range (blowupCoordinate i)) :=
    Algebra.subset_adjoin (Set.mem_range_self j)
  by_cases hji : j = i
  · subst j
    simpa [blowupCoordinate] using hi
  · have hh := Subalgebra.mul_mem _ hj hi
    simpa [blowupCoordinate, hji, coordinate_ne_zero i] using hh

lemma ratios_adjoin_eq (i : Fin 3) :
    Algebra.adjoin ℂ (Set.range fun j => coordinate j / coordinate i) =
      Algebra.adjoin ℂ (blowupCoordinate i '' ({i}ᶜ : Set (Fin 3))) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨j,rfl⟩
    by_cases hji : j=i
    · subst j
      change coordinate i / coordinate i ∈ _
      rw [div_self (coordinate_ne_zero i)]
      exact (Algebra.adjoin ℂ (blowupCoordinate i '' ({i}ᶜ : Set (Fin 3)))).one_mem
    · apply Algebra.subset_adjoin
      exact ⟨j, by simpa using hji, by simp only [blowupCoordinate, ite_eq_right hji]⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨j,hj,rfl⟩
    have hji : j ≠ i := by simpa using hj
    simp only [blowupCoordinate, ite_eq_right hji]
    exact Algebra.subset_adjoin (Set.mem_range_self j)

lemma radial_transcendental (i : Fin 3) :
    Transcendental (planeFieldAlg i).range (coordinate i) := by
  rw [planeField_range, ratios_adjoin_eq]
  simpa [blowupCoordinate] using
    (blowupCoordinate_independent i).transcendental_adjoin (s := {i}ᶜ) (i := i) (by simp)

lemma planePolynomial_injective (i : Fin 3) :
    Function.Injective (Polynomial.eval₂RingHom (planeField i) (coordinate i)) := by
  exact Polynomial.eval₂RingHom_injective_of_range_transcendental (planeFieldAlg i)
    (planeField_injective i) (coordinate i) (radial_transcendental i)

end SourcePullbackChart

end


/-! Local cone evaluation on the affine tensor charts of the literal source
pullback. The section variables and S-module structure are the same as those
in the finite projective morphism, not independently chosen parameters. -/
noncomputable section
open _root_.Polynomial _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open SectionCompletion
abbrev surfaceChart (i : Fin 3) := homogeneousChart ExplicitCone.pieces
  (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)
instance surfaceChartScalar (i : Fin 3) : Algebra ℂ (surfaceChart i) :=
  homogeneousChartScalarAlgebra ExplicitCone.pieces
    (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)
abbrev sectionRing : Type := polynomials ExplicitCone.pieces
abbrev parameterMap : S →ₐ[ℂ] sectionRing :=
  linearPolynomialMap ExplicitCone.pieces ExplicitCone.projectiveParameter
    ExplicitCone.projectiveParameter_mem
abbrev surfaceDirectionMap (i : Fin 3) : planeChart i →+* surfaceChart i :=
  linearChartMap ExplicitCone.pieces ExplicitCone.projectiveParameter
    ExplicitCone.projectiveParameter_mem i

instance surfaceChartPlaneAlgebra (i : Fin 3) : Algebra (planeChart i) (surfaceChart i) :=
  (surfaceDirectionMap i).toAlgebra
instance chartPlaneAlgebra (i : Fin 3) : Algebra (planeChart i) (chart i) :=
  (directionMap i).toAlgebra

abbrev pullbackChart (i : Fin 3) := surfaceChart i ⊗[planeChart i] chart i

def surfaceIn (i : Fin 3) : surfaceChart i →+* pullbackChart i :=
  Algebra.TensorProduct.includeLeftRingHom

def blowupIn (i : Fin 3) : chart i →+* pullbackChart i :=
  Algebra.TensorProduct.includeRight.toRingHom

lemma tensor_balance (i : Fin 3) (a : planeChart i) :
    surfaceIn i (surfaceDirectionMap i a) = blowupIn i (directionMap i a) := by
  exact congrArg (fun f : planeChart i →+* pullbackChart i => f a)
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

def fiberParameter (i : Fin 3) : pullbackChart i := blowupIn i (baseMap i (MvPolynomial.X i))

/-- The section evaluation, in the coordinate ring of the source's actual
fiber product of affine charts. -/
def coneEvaluation (i : Fin 3) : sectionRing →+* pullbackChart i :=
  (Polynomial.eval₂RingHom (surfaceIn i) (fiberParameter i)).comp
    (chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)).toRingHom

lemma coneEvaluation_scalar (i : Fin 3) (a : ℂ) :
    coneEvaluation i (algebraMap ℂ sectionRing a) =
      surfaceIn i ((@algebraMap ℂ (surfaceChart i) _ _ (surfaceChartScalar i)) a) := by
  change Polynomial.eval₂ (surfaceIn i) (fiberParameter i)
    (chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)
      (algebraMap ℂ sectionRing a)) = _
  rw [(chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)).commutes a]
  change Polynomial.eval₂ _ _ (C _) = _
  rw [Polynomial.eval₂_C]


lemma surfaceDirectionMap_ratio (i j : Fin 3) :
    surfaceDirectionMap i (polynomialChartDehom i (MvPolynomial.X j)) =
      dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)
        (linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter j)
          (ExplicitCone.projectiveParameter_mem j)) := by
  have h := congrArg (fun f : S →ₐ[ℂ] surfaceChart i => f (MvPolynomial.X j))
    (linearChartMap_dehom ExplicitCone.pieces ExplicitCone.projectiveParameter
      ExplicitCone.projectiveParameter_mem i (ExplicitCone.projectiveParameter_ne_zero i))
  simp only [AlgHom.comp_apply, linearPolynomialMap, MvPolynomial.aeval_X] at h
  convert h using 1 <;> rfl


lemma coneEvaluation_variable (i j : Fin 3) :
    coneEvaluation i (parameterMap (MvPolynomial.X j)) =
      blowupIn i (baseMap i (MvPolynomial.X j)) := by
  have hpj : parameterMap (MvPolynomial.X j) =
      linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter j)
        (ExplicitCone.projectiveParameter_mem j) := by
    simp only [parameterMap, linearPolynomialMap, MvPolynomial.aeval_X, linearSection]
  rw [hpj]
  change Polynomial.eval₂ (surfaceIn i) (fiberParameter i)
    (chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)
      (linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter j)
        (ExplicitCone.projectiveParameter_mem j))) = _
  rw [chartEvaluation_linearSection]
  simp only [eval₂_mul, eval₂_C, eval₂_X]
  rw [← surfaceDirectionMap_ratio, tensor_balance]
  change blowupIn i _ * blowupIn i _ = _
  rw [← map_mul, ratio_relation]

/-- Exact S-compatibility: evaluation commutes with the blowdown variables,
including the scalars. It can therefore be base changed by S→C[[x₀,x₁,x₂]]. -/
lemma coneEvaluation_comp_parameters (i : Fin 3) :
    (coneEvaluation i).comp parameterMap.toRingHom = (blowupIn i).comp (baseMap i) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    change coneEvaluation i (parameterMap (algebraMap ℂ S a)) = _
    rw [parameterMap.commutes, coneEvaluation_scalar]
    rw [← linearChartMap_scalar ExplicitCone.pieces ExplicitCone.projectiveParameter
        ExplicitCone.projectiveParameter_mem i a]
    rw [tensor_balance, directionMap_scalar]
  · intro j
    exact coneEvaluation_variable i j

end SourcePullbackChart

end


/-! The affine charts of the blowup are polynomial rings over the projective direction charts. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization _root_.MvPolynomial _root_.OAI.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance lineFieldRing : Ring K := (inferInstance : CommRing K).toRing

def planePolynomialToRees (i : Fin 3) : Polynomial (planeChart i) →+* chart i :=
  Polynomial.eval₂RingHom (directionMap i) (baseMap i (MvPolynomial.X i))

def planePolynomialField (i : Fin 3) : Polynomial (planeChart i) →+* K :=
  Polynomial.eval₂RingHom (planeField i) (coordinate i)

lemma planePolynomialToRees_field (i : Fin 3) :
    (reesField i).comp (planePolynomialToRees i) = planePolynomialField i := by
  apply Polynomial.ringHom_ext
  · intro a
    change reesField i (Polynomial.eval₂ (directionMap i) _ (Polynomial.C a)) =
      Polynomial.eval₂ (planeField i) _ (Polynomial.C a)
    rw [Polynomial.eval₂_C, Polynomial.eval₂_C, reesField_direction]
  · change reesField i (Polynomial.eval₂ (directionMap i) _ Polynomial.X) =
      Polynomial.eval₂ (planeField i) _ Polynomial.X
    rw [Polynomial.eval₂_X, Polynomial.eval₂_X, reesField_base]
    rfl

lemma planePolynomialToRees_injective (i : Fin 3) :
    Function.Injective (planePolynomialToRees i) := by
  intro a b h
  apply planePolynomial_injective i
  have hh := congrArg (reesField i) h
  change ((reesField i).comp (planePolynomialToRees i)) a =
    ((reesField i).comp (planePolynomialToRees i)) b at hh
  rw [planePolynomialToRees_field] at hh
  exact hh

lemma polynomialField_ratio_mem (i j : Fin 3) :
    coordinate j / coordinate i ∈ (planePolynomialField i).range := by
  refine ⟨Polynomial.C (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)), ?_⟩
  change Polynomial.eval₂ _ _ (Polynomial.C _) = _
  rw [Polynomial.eval₂_C, planeField_ratio]

lemma polynomialField_coordinate_mem (i j : Fin 3) :
    coordinate j ∈ (planePolynomialField i).range := by
  have hx : coordinate i ∈ (planePolynomialField i).range :=
    ⟨Polynomial.X, Polynomial.eval₂_X _ _⟩
  simpa only [div_mul_cancel₀ _ (coordinate_ne_zero i)] using
    (planePolynomialField i).range.mul_mem (polynomialField_ratio_mem i j) hx

lemma polynomialField_base_mem (i : Fin 3) (a : S) :
    algebraMap S K a ∈ (planePolynomialField i).range := by
  induction a using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Polynomial.C (algebraMap ℂ (planeChart i) c), ?_⟩
    change Polynomial.eval₂ _ _ (Polynomial.C _) = _
    rw [Polynomial.eval₂_C, planeField_scalar]
    exact (IsScalarTower.algebraMap_apply ℂ S K c).symm
  | add a b ha hb =>
    simpa only [map_add] using (planePolynomialField i).range.add_mem ha hb
  | mul_X a j ha =>
    simpa only [map_mul, coordinate] using
      (planePolynomialField i).range.mul_mem ha (polynomialField_coordinate_mem i j)

lemma polynomialField_scaled_mem (i : Fin 3) (n : ℕ) (a : S)
    (ha : a ∈ origin ^ n) :
    algebraMap S K a / coordinate i ^ n ∈ (planePolynomialField i).range := by
  have hspan (b : S) (hb : b ∈ origin) :
      algebraMap S K b / coordinate i ∈ (planePolynomialField i).range := by
    change b ∈ Ideal.span (Set.range (MvPolynomial.X : Fin 3 → S)) at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨j, rfl⟩ := hb
      exact polynomialField_ratio_mem i j
    | zero => simp
    | add b c hb hc h₁ h₂ =>
      simpa only [map_add, add_div] using (planePolynomialField i).range.add_mem h₁ h₂
    | smul r b hb h =>
      change algebraMap S K (r * b) / coordinate i ∈ _
      rw [map_mul, mul_div_assoc]
      exact (planePolynomialField i).range.mul_mem (polynomialField_base_mem i r) h
  induction n generalizing a with
  | zero => simpa using polynomialField_base_mem i a
  | succ n hn =>
    rw [pow_succ'] at ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro a ha b hb
      change algebraMap S K (a * b) / coordinate i ^ (n+1) ∈ _
      rw [map_mul, pow_succ', ← div_mul_div_comm]
      exact (planePolynomialField i).range.mul_mem (hspan a ha) (hn b hb)
    · intro a b ha hb
      simpa only [map_add, add_div] using (planePolynomialField i).range.add_mem ha hb

lemma planePolynomialToRees_surjective (i : Fin 3) :
    Function.Surjective (planePolynomialToRees i) := by
  intro x
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective grades (sourceSection_homogeneous i) x
  obtain ⟨q,hq⟩ := polynomialField_scaled_mem i n (a.val.coeff n) (a.property n)
  refine ⟨q, reesField_injective i ?_⟩
  rw [reesField_mk]
  exact (congrArg (fun f : Polynomial (planeChart i) →+* K => f q)
    (planePolynomialToRees_field i)).trans hq

/-- The actual Rees chart is the affine line over its actual plane chart. -/
def planePolynomialEquiv (i : Fin 3) : Polynomial (planeChart i) ≃ₐ[planeChart i] chart i :=
  AlgEquiv.ofBijective
    { planePolynomialToRees i with
      commutes' := by
        intro a
        exact Polynomial.eval₂_C _ _ }
    ⟨planePolynomialToRees_injective i, planePolynomialToRees_surjective i⟩

@[simp] lemma planePolynomialEquiv_C (i : Fin 3) (a : planeChart i) :
    planePolynomialEquiv i (Polynomial.C a) = directionMap i a := Polynomial.eval₂_C _ _

@[simp] lemma planePolynomialEquiv_X (i : Fin 3) :
    planePolynomialEquiv i Polynomial.X = baseMap i (MvPolynomial.X i) := Polynomial.eval₂_X _ _

end SourcePullbackChart

end


/-! The affine-line base-change equivalence used for the literal source model. -/
noncomputable section
open TensorProduct
namespace Polynomial
open scoped _root_.Polynomial
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

def scalarBaseChangeEquiv : A ⊗[R] Polynomial R ≃ₐ[A] Polynomial A :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
    (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
      ((MvPolynomial.algebraTensorAlgEquiv R A).trans
        (MvPolynomial.uniqueAlgEquiv A Unit))

@[simp] lemma scalarBaseChangeEquiv_tmul_C (a : A) (r : R) :
    scalarBaseChangeEquiv R A (a ⊗ₜ[R] _root_.Polynomial.C r) = _root_.Polynomial.C (a * algebraMap R A r) := by
  simp [scalarBaseChangeEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul,
    Algebra.smul_def]

@[simp] lemma scalarBaseChangeEquiv_one_tmul_X :
    scalarBaseChangeEquiv R A (1 ⊗ₜ[R] _root_.Polynomial.X) = _root_.Polynomial.X := by
  simp [scalarBaseChangeEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]

@[simp] lemma scalarBaseChangeEquiv_symm_C (a : A) :
    (scalarBaseChangeEquiv R A).symm (_root_.Polynomial.C a) = a ⊗ₜ[R] 1 := by
  apply (scalarBaseChangeEquiv R A).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa using (scalarBaseChangeEquiv_tmul_C R A a 1).symm

@[simp] lemma scalarBaseChangeEquiv_symm_X :
    (scalarBaseChangeEquiv R A).symm _root_.Polynomial.X = 1 ⊗ₜ[R] _root_.Polynomial.X := by
  apply (scalarBaseChangeEquiv R A).injective
  rw [AlgEquiv.apply_symm_apply, scalarBaseChangeEquiv_one_tmul_X]

end Polynomial

end


/-! Literal line-bundle coordinates on the affine tensor charts of W₀.
They are compatible with the already constructed cone evaluation. -/
noncomputable section
open TensorProduct _root_.Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance linePullbackCommRing (i : Fin 3) : CommRing (pullbackChart i) := inferInstance
local instance linePullbackSemiring (i : Fin 3) : Semiring (pullbackChart i) := (linePullbackCommRing i).toSemiring

/-- The source pullback is locally the affine line over the surface's own
homogeneous chart, rather than a merely posited replacement scheme. -/
def pullbackPolynomialEquiv (i : Fin 3) :
    pullbackChart i ≃ₐ[surfaceChart i] Polynomial (surfaceChart i) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : surfaceChart i ≃ₐ[surfaceChart i] surfaceChart i)
    (planePolynomialEquiv i).symm).trans
      (Polynomial.scalarBaseChangeEquiv (planeChart i) (surfaceChart i))

@[simp] lemma pullbackPolynomialEquiv_surface (i : Fin 3) (a : surfaceChart i) :
    pullbackPolynomialEquiv i (surfaceIn i a) = C a := by
  exact (pullbackPolynomialEquiv i).commutes a

@[simp] lemma pullbackPolynomialEquiv_fiber (i : Fin 3) :
    pullbackPolynomialEquiv i (fiberParameter i) = X := by
  have hh : (planePolynomialEquiv i).symm (baseMap i (MvPolynomial.X i)) = X := by
    apply (planePolynomialEquiv i).injective
    simp
  simp only [fiberParameter, blowupIn, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply, pullbackPolynomialEquiv,
    AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, map_one, hh,
    Polynomial.scalarBaseChangeEquiv_one_tmul_X]

lemma pullbackPolynomialEquiv_coefficientMap (i : Fin 3) :
    (pullbackPolynomialEquiv i).toRingHom.comp (surfaceIn i) = Polynomial.C := by
  apply RingHom.ext
  intro a
  exact pullbackPolynomialEquiv_surface i a

lemma pullbackPolynomialEquiv_eval (i : Fin 3) (q : Polynomial (surfaceChart i)) :
    pullbackPolynomialEquiv i (Polynomial.eval₂ (surfaceIn i) (fiberParameter i) q) = q := by
  change (pullbackPolynomialEquiv i).toRingHom (Polynomial.eval₂ _ _ q) = q
  rw [Polynomial.hom_eval₂, pullbackPolynomialEquiv_coefficientMap]
  change Polynomial.eval₂ Polynomial.C (pullbackPolynomialEquiv i (fiberParameter i)) q = q
  rw [pullbackPolynomialEquiv_fiber, Polynomial.eval₂_C_X]

/-- Exact coordinate identity for the geometric map already glued on W₀. -/
lemma pullbackPolynomialEquiv_coneEvaluation (i : Fin 3) (b : sectionRing) :
    pullbackPolynomialEquiv i (coneEvaluation i b) =
      SectionCompletion.chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) b :=
  pullbackPolynomialEquiv_eval i _

end SourcePullbackChart

end


/-! Inverting the fiber coordinate does not kill a polynomial. Used to
prove the source punctured-chart isomorphism without a domain assumption. -/
namespace Polynomial
open scoped _root_.Polynomial
variable (R : Type*) [CommRing R]
lemma awayX_injective : Function.Injective
    (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr
    Polynomial.isRegular_X.mem_nonZeroDivisors)
end Polynomial


/-! The source's explicit equation T[1/s] = D_s[t,t⁻¹], without generation
in degree one. This is required to show the constructed p is a punctured
isomorphism, not merely a proper morphism. -/
noncomputable section
open _root_.Polynomial _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (c : K) (hc : c ∈ T 1) (hn : c ≠ 0)

abbrev conePuncture := Localization.Away (linearSection T c hc)
abbrev linePuncture := Localization.Away (X : Polynomial (homogeneousChart T c hc))

local instance puncturedChartAlgebra :
    Algebra (homogeneousChart T c hc) (conePuncture T c hc) :=
  HomogeneousLocalization.homogeneousLocalizationAlgebra

def coneCoefficientInclusion : homogeneousChart T c hc →+* conePuncture T c hc :=
  algebraMap (homogeneousChart T c hc) (conePuncture T c hc)

def punctureBase : polynomials T →+* linePuncture T c hc :=
  (algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc)).comp
    (chartEvaluation T c hc hn).toRingHom

lemma punctureBase_section :
    punctureBase T c hc hn (linearSection T c hc) =
      algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc) X := by
  simp only [punctureBase, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    chartEvaluation_parameter]

def punctureEvaluation : conePuncture T c hc →+* linePuncture T c hc :=
  Localization.awayLift (punctureBase T c hc hn) (linearSection T c hc)
    (by rw [punctureBase_section]; exact IsLocalization.Away.algebraMap_isUnit X)

@[simp] lemma punctureEvaluation_base (a : polynomials T) :
    punctureEvaluation T c hc hn (algebraMap (polynomials T) (conePuncture T c hc) a) =
      punctureBase T c hc hn a := by
  simp only [punctureEvaluation, Localization.awayLift, IsLocalization.Away.lift_eq]

lemma dehomogenize_homogeneous_mk (n : ℕ) (a : polynomials T)
    (ha : a ∈ homogeneous T (n • 1)) :
    dehomogenize T c hc hn a = Away.mk (homogeneous T)
      (linearSection_homogeneous T c hc) n a ha := by
  apply homogeneousChartMap_injective T c hc hn
  rw [homogeneousChartMap_dehomogenize, homogeneousChartMap_mk,
    evaluateInv_homogeneous T c n a ha]

lemma homogeneousFraction_spec (n : ℕ) (a : polynomials T)
    (ha : a ∈ homogeneous T (n • 1)) :
    coneCoefficientInclusion T c hc
      (Away.mk (homogeneous T) (linearSection_homogeneous T c hc) n a ha) *
        (algebraMap (polynomials T) (conePuncture T c hc) (linearSection T c hc)) ^ n =
      algebraMap (polynomials T) (conePuncture T c hc) a := by
  simp only [coneCoefficientInclusion, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk', ← map_pow]
  exact IsLocalization.mk'_spec (conePuncture T c hc) a
    (⟨linearSection T c hc ^ n, n, rfl⟩ : Submonoid.powers (linearSection T c hc))

lemma punctureEvaluation_coefficient (d : homogeneousChart T c hc) :
    punctureEvaluation T c hc hn
      (coneCoefficientInclusion T c hc d) =
      algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc) (C d) := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (homogeneous T) (linearSection_homogeneous T c hc) d
  apply ((IsLocalization.Away.algebraMap_isUnit (S := linePuncture T c hc)
    (X : Polynomial (homogeneousChart T c hc))).pow n).mul_left_inj.mp
  have h := congrArg (punctureEvaluation T c hc hn) (homogeneousFraction_spec T c hc n a ha)
  rw [map_mul, map_pow, punctureEvaluation_base, punctureEvaluation_base,
    punctureBase_section] at h
  rw [h]
  change algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc)
      (chartEvaluation T c hc hn a) = _
  rw [chartEvaluation_homogeneous T c hc hn n a (by simpa using ha),
    dehomogenize_homogeneous_mk T c hc hn n a ha,
    ← map_pow, ← map_mul, C_mul_X_pow_eq_monomial]

lemma punctureBase_injective : Function.Injective (punctureBase T c hc hn) := by
  intro a b h
  apply chartEvaluation_injective T c hc hn
  exact Polynomial.awayX_injective (homogeneousChart T c hc) h

lemma punctureEvaluation_injective : Function.Injective (punctureEvaluation T c hc hn) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (linearSection T c hc)) (punctureEvaluation T c hc hn)).mpr
  intro a b
  constructor
  · exact congrArg (punctureEvaluation T c hc hn)
  · intro h
    rw [punctureEvaluation_base, punctureEvaluation_base] at h
    exact congrArg (algebraMap (polynomials T) (conePuncture T c hc))
      (punctureBase_injective T c hc hn h)

def lineToConePolynomial : Polynomial (homogeneousChart T c hc) →+* conePuncture T c hc :=
  Polynomial.eval₂RingHom (coneCoefficientInclusion T c hc)
    (algebraMap (polynomials T) (conePuncture T c hc) (linearSection T c hc))

def lineToConePuncture : linePuncture T c hc →+* conePuncture T c hc :=
  Localization.awayLift (lineToConePolynomial T c hc) X (by
    change IsUnit (Polynomial.eval₂ _ _ X)
    rw [Polynomial.eval₂_X]
    exact IsLocalization.Away.algebraMap_isUnit (linearSection T c hc))

lemma punctureEvaluation_lineToConePolynomial :
    (punctureEvaluation T c hc hn).comp (lineToConePolynomial T c hc) =
      algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc) := by
  apply Polynomial.ringHom_ext
  · intro d
    change punctureEvaluation T c hc hn (Polynomial.eval₂ _ _ (C d)) = _
    rw [Polynomial.eval₂_C, punctureEvaluation_coefficient]
  · change punctureEvaluation T c hc hn (Polynomial.eval₂ _ _ X) = _
    rw [Polynomial.eval₂_X, punctureEvaluation_base, punctureBase_section]

lemma punctureEvaluation_rightInverse :
    Function.RightInverse (lineToConePuncture T c hc) (punctureEvaluation T c hc hn) := by
  have hh : (punctureEvaluation T c hc hn).comp (lineToConePuncture T c hc) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : Polynomial (homogeneousChart T c hc)))
    rw [RingHom.comp_assoc]
    have hm : (lineToConePuncture T c hc).comp
        (algebraMap (Polynomial (homogeneousChart T c hc)) (linePuncture T c hc)) =
        lineToConePolynomial T c hc := by
      simp only [lineToConePuncture, Localization.awayLift, IsLocalization.Away.lift_comp]
    rw [hm, punctureEvaluation_lineToConePolynomial, RingHom.id_comp]
  intro d
  exact congrArg (fun f : linePuncture T c hc →+* linePuncture T c hc => f d) hh

/-- The actual cone puncture agrees with the actual punctured line chart.
This proof makes no degree-one generation assumption. -/
def punctureEquiv : conePuncture T c hc ≃+* linePuncture T c hc :=
  RingEquiv.ofBijective (punctureEvaluation T c hc hn)
    ⟨punctureEvaluation_injective T c hc hn,
      (punctureEvaluation_rightInverse T c hc hn).surjective⟩

end SectionCompletion

end


/-! The actual cone-evaluation morphism is an isomorphism on each section
puncture of its literal source chart. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory _root_.Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open SectionCompletion
local instance puncturePullbackCommRing (i : Fin 3) : CommRing (pullbackChart i) := inferInstance
local instance puncturePullbackSemiring (i : Fin 3) : Semiring (pullbackChart i) :=
  (puncturePullbackCommRing i).toSemiring

abbrev coneSection (i : Fin 3) : sectionRing :=
  linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
    (ExplicitCone.projectiveParameter_mem i)

lemma coneSection_eq (i : Fin 3) : coneSection i = parameterMap (MvPolynomial.X i) := by
  simp only [coneSection, parameterMap, linearPolynomialMap, MvPolynomial.aeval_X, linearSection]

lemma pullbackPolynomialEquiv_coneSection (i : Fin 3) :
    pullbackPolynomialEquiv i (coneEvaluation i (coneSection i)) = X := by
  rw [pullbackPolynomialEquiv_coneEvaluation, chartEvaluation_parameter]

abbrev evaluationPuncture (i : Fin 3) := Localization.Away (coneEvaluation i (coneSection i))
abbrev polynomialPuncture (i : Fin 3) := linePuncture ExplicitCone.pieces
  (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)

local instance evaluationPunctureRing (i : Fin 3) : CommRing (evaluationPuncture i) := inferInstance
local instance conePunctureRing (i : Fin 3) : CommRing (Localization.Away (coneSection i)) := inferInstance
local instance polynomialPunctureRing (i : Fin 3) : CommRing (polynomialPuncture i) := inferInstance

/-- Localization of the actual line-bundle ring chart. -/
def pullbackPunctureEquiv (i : Fin 3) : evaluationPuncture i ≃+* polynomialPuncture i :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coneEvaluation i (coneSection i)))
    (T := Submonoid.powers (X : Polynomial (surfaceChart i)))
    (evaluationPuncture i) (polynomialPuncture i)
    (pullbackPolynomialEquiv i).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (pullbackPolynomialEquiv_coneSection i))

lemma pullbackPunctureEquiv_base (i : Fin 3) (b : pullbackChart i) :
    (pullbackPunctureEquiv i).toRingHom
      (algebraMap (pullbackChart i) (evaluationPuncture i) b) =
      algebraMap (Polynomial (surfaceChart i)) (polynomialPuncture i)
        (pullbackPolynomialEquiv i b) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (pullbackPolynomialEquiv_coneSection i)) b

lemma pullbackPunctureEquiv_awayMap (i : Fin 3) :
    (pullbackPunctureEquiv i).toRingHom.comp
      (Localization.awayMap (coneEvaluation i) (coneSection i)) =
    punctureEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneSection i))
  apply RingHom.ext
  intro b
  simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq, pullbackPunctureEquiv_base,
    punctureEvaluation_base, punctureBase, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact congrArg (algebraMap (Polynomial (surfaceChart i)) (polynomialPuncture i))
    (pullbackPolynomialEquiv_coneEvaluation i b)

lemma awayMap_eq_punctureEquiv (i : Fin 3) :
    Localization.awayMap (coneEvaluation i) (coneSection i) =
    ((punctureEquiv ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)).trans
        (pullbackPunctureEquiv i).symm).toRingHom := by
  apply RingHom.ext
  intro b
  apply (pullbackPunctureEquiv i).injective
  exact (RingHom.congr_fun (pullbackPunctureEquiv_awayMap i) b).trans
    (RingEquiv.apply_symm_apply (pullbackPunctureEquiv i) _).symm

/-- Literal local geometric isomorphism over the actual s_i, not over a
hypothetical degree-one generated cone. -/
lemma coneEvaluation_restrict_isIso (i : Fin 3) :
    IsIso ((Spec.map (CommRingCat.ofHom (coneEvaluation i))) ∣_
      (PrimeSpectrum.basicOpen (coneSection i))) := by
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (coneEvaluation i) (coneSection i))) := by
    rw [awayMap_eq_punctureEquiv]
    exact inferInstanceAs (IsIso
      ((punctureEquiv ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)).trans
          (pullbackPunctureEquiv i).symm).toCommRingCatIso.hom)
  exact (Arrow.isIso_iff_isIso_of_isIso
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (coneEvaluation i)) (coneSection i)).hom).mpr
      inferInstance

end SourcePullbackChart

end


/-! The literal source affine tensor charts are open subschemes of W₀.
These maps connect the new cone evaluation to the manuscript's actual fiber
product rather than to a different ordinary Rees resolution. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open SectionCompletion

def planeIota (i : Fin 3) : Spec (.of (planeChart i)) ⟶ ExplicitCone.plane :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i) zero_lt_one

def blowupIota (i : Fin 3) : Spec (.of (chart i)) ⟶ KummerSourceModel.V₀ :=
  Proj.awayι grades (sourceSection i) (sourceSection_homogeneous i) zero_lt_one

def surfaceIota (i : Fin 3) : Spec (.of (surfaceChart i)) ⟶ ExplicitCone.projectiveSurface :=
  Proj.awayι (homogeneous ExplicitCone.pieces)
    (linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i))
    (linearSection_homogeneous ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i)) zero_lt_one

instance (i : Fin 3) : IsOpenImmersion (planeIota i) := by
  rw [planeIota.eq_1]
  unfold Proj.awayι
  infer_instance
instance (i : Fin 3) : IsOpenImmersion (blowupIota i) := by unfold blowupIota; infer_instance
instance (i : Fin 3) : IsOpenImmersion (surfaceIota i) := by
  rw [surfaceIota.eq_1]
  unfold Proj.awayι
  refine @IsOpenImmersion.comp _ _ _ _ _ inferInstance ?_
  unfold Scheme.Opens.ι
  exact IsOpenImmersion.ofRestrict _ _

lemma blowup_chart_square (i : Fin 3) :
    blowupIota i ≫ KummerSourceModel.direction =
      Spec.map (CommRingCat.ofHom (directionMap i)) ≫ planeIota i := by
  exact Proj.radical_awayι_comp_map KummerSourceModel.projectionGradedMap.toGradedRingHom
    KummerSourceModel.irrelevant_le_radical zero_lt_one (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i)

lemma surface_chart_square (i : Fin 3) :
    surfaceIota i ≫ ExplicitCone.projectiveNormalization =
      Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)) ≫ planeIota i := by
  have h := linearProjectiveMap_chart ExplicitCone.pieces ExplicitCone.projectiveParameter
    ExplicitCone.projectiveParameter_mem ExplicitCone.projectiveParameter_finite i
  have aux (q : sectionRing)
      (hq : q = (linearGradedMap ExplicitCone.pieces ExplicitCone.projectiveParameter
        ExplicitCone.projectiveParameter_mem).toGradedRingHom (MvPolynomial.X i))
      (hqmem : q ∈ homogeneous ExplicitCone.pieces 1)
      (hc : Submonoid.powers (MvPolynomial.X i) ≤ (Submonoid.powers q).comap
        (linearGradedMap ExplicitCone.pieces ExplicitCone.projectiveParameter
          ExplicitCone.projectiveParameter_mem).toGradedRingHom) :
      Proj.awayι (homogeneous ExplicitCone.pieces) q hqmem zero_lt_one ≫
          ExplicitCone.projectiveNormalization =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map
          (linearGradedMap ExplicitCone.pieces ExplicitCone.projectiveParameter
            ExplicitCone.projectiveParameter_mem).toGradedRingHom hc)) ≫ planeIota i := by
    subst q
    exact h
  exact aux _ (linearGradedMap_X ExplicitCone.pieces ExplicitCone.projectiveParameter
    ExplicitCone.projectiveParameter_mem i).symm _ _

/-- The open chart of the literal source fiber product. -/
def pullbackIota (i : Fin 3) : Spec (.of (pullbackChart i)) ⟶ KummerSourceModel.W₀ :=
  (pullbackSpecIso (planeChart i) (surfaceChart i) (chart i)).inv ≫
    pullback.map
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (Spec.map (CommRingCat.ofHom (directionMap i)))
      ExplicitCone.projectiveNormalization KummerSourceModel.direction
      (surfaceIota i) (blowupIota i) (planeIota i)
      (surface_chart_square i).symm (blowup_chart_square i).symm

instance (i : Fin 3) : IsOpenImmersion (pullbackIota i) := by
  unfold pullbackIota
  infer_instance

@[reassoc] lemma pullbackIota_surface (i : Fin 3) :
    pullbackIota i ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (surfaceIn i)) ≫ surfaceIota i := by
  simp only [pullbackIota, Category.assoc, pullback.map, pullback.lift_fst,
    ]
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ surfaceIota i)
    (pullbackSpecIso_inv_fst (planeChart i) (surfaceChart i) (chart i))

@[reassoc] lemma pullbackIota_blowup (i : Fin 3) :
    pullbackIota i ≫ KummerSourceModel.g₀ =
      Spec.map (CommRingCat.ofHom (blowupIn i)) ≫ blowupIota i := by
  simp only [pullbackIota, KummerSourceModel.g₀, Category.assoc, pullback.map, pullback.lift_snd,
    ]
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ blowupIota i)
    (pullbackSpecIso_inv_snd (planeChart i) (surfaceChart i) (chart i))

lemma surface_isPullback (i : Fin 3) :
    IsPullback (surfaceIota i) (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      ExplicitCone.projectiveNormalization (planeIota i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact surface_chart_square i
  · dsimp only [surfaceIota, planeIota]
    erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    change Proj.basicOpen (homogeneous ExplicitCone.pieces)
      ((linearGradedMap ExplicitCone.pieces ExplicitCone.projectiveParameter
        ExplicitCone.projectiveParameter_mem) (MvPolynomial.X i)) = _
    rw [linearGradedMap_X]

lemma blowup_isPullback (i : Fin 3) :
    IsPullback (blowupIota i) (Spec.map (CommRingCat.ofHom (directionMap i)))
      KummerSourceModel.direction (planeIota i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact blowup_chart_square i
  · dsimp only [blowupIota, planeIota]
    erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    rfl

/-- The exact three standard plane charts. -/
def planeCover : ExplicitCone.plane.OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) MvPolynomial.X
    (fun i => MvPolynomial.isHomogeneous_X ℂ i) (fun _ => zero_lt_one)
    polynomial_irrelevant_le).openCover

@[simp] lemma planeCover_f (i : Fin 3) : planeCover.f i = planeIota i := rfl

abbrev baseChangeCover : KummerSourceModel.W₀.OpenCover :=
  Scheme.Pullback.openCoverOfBase planeCover ExplicitCone.projectiveNormalization
    KummerSourceModel.direction

/-- Chartwise comparison with the built-in base-changed open cover. -/
def pullbackChartIso (i : Fin 3) : Spec (.of (pullbackChart i)) ≅ baseChangeCover.X i := by
  let es := (surface_isPullback i).isoPullback
  let eb := (blowup_isPullback i).isoPullback
  have : IsIso es.hom := es.isIso_hom
  have : IsIso eb.hom := eb.isIso_hom
  let hs : Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)) ≫ 𝟙 _ =
      es.hom ≫ pullback.snd ExplicitCone.projectiveNormalization (planeIota i) := by
    simpa only [Category.comp_id] using (surface_isPullback i).isoPullback_hom_snd.symm
  let hb : Spec.map (CommRingCat.ofHom (directionMap i)) ≫ 𝟙 _ =
      eb.hom ≫ pullback.snd KummerSourceModel.direction (planeIota i) := by
    simpa only [Category.comp_id] using (blowup_isPullback i).isoPullback_hom_snd.symm
  let m := pullback.map
    (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
    (Spec.map (CommRingCat.ofHom (directionMap i)))
    (pullback.snd ExplicitCone.projectiveNormalization (planeIota i))
    (pullback.snd KummerSourceModel.direction (planeIota i))
    es.hom eb.hom (𝟙 _) hs hb
  have hm : IsIso m := by
    dsimp only [m]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact (pullbackSpecIso (planeChart i) (surfaceChart i) (chart i)).symm ≪≫
    @asIso _ _ _ _ m hm

lemma pullbackChartIso_hom_iota (i : Fin 3) :
    (pullbackChartIso i).hom ≫ baseChangeCover.f i = pullbackIota i := by
  change (pullbackChartIso i).hom ≫
    (Scheme.Pullback.openCoverOfBase planeCover ExplicitCone.projectiveNormalization
      KummerSourceModel.direction).f i = _
  erw [Scheme.Pullback.openCoverOfBase_f]
  simp only [planeCover_f]
  erw [pullbackChartIso.eq_1]
  dsimp only [asIso, Iso.trans_hom, Iso.symm_hom, pullbackIota]
  erw [Category.assoc, pullback.map_comp]
  apply congrArg (fun h : pullback
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (Spec.map (CommRingCat.ofHom (directionMap i))) ⟶ KummerSourceModel.W₀ =>
    (pullbackSpecIso (planeChart i) (surfaceChart i) (chart i)).inv ≫ h)
  apply pullback.hom_ext
  · simp only [pullback.map, pullback.lift_fst]
    exact congrArg (fun h => pullback.fst
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (Spec.map (CommRingCat.ofHom (directionMap i))) ≫ h)
      (surface_isPullback i).isoPullback_hom_fst
  · simp only [pullback.map, pullback.lift_snd]
    exact congrArg (fun h => pullback.snd
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (Spec.map (CommRingCat.ofHom (directionMap i))) ≫ h)
      (blowup_isPullback i).isoPullback_hom_fst

/-- An affine open cover of the literal source by the tensor rings on
which coneEvaluation was constructed. -/
def sourceCover : KummerSourceModel.W₀.OpenCover where
  I₀ := Fin 3
  X i := Spec (.of (pullbackChart i))
  f := pullbackIota
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨y, hy⟩ := baseChangeCover.covers x
    let i : Fin 3 := baseChangeCover.idx x
    change baseChangeCover.X i at y
    change (baseChangeCover.f i) y = x at hy
    refine ⟨i, (pullbackChartIso i).inv y, ?_⟩
    change pullbackIota i ((pullbackChartIso i).inv y) = x
    erw [← pullbackChartIso_hom_iota, Scheme.Hom.comp_apply]
    simpa using hy

end SourcePullbackChart

end

end OAI
