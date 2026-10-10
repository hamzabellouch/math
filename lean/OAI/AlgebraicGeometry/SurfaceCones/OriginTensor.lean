import OAI.AlgebraicGeometry.SurfaceCones.SpecCoordinates

namespace OAI


/-! Coordinate ring of the actual closed fiber of V₀: its literal tensor
product with C over S is the plane chart, via evaluation of the fiber
coordinate at zero. No blowup/line-bundle isomorphism is assumed globally. -/
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance originTensorChartCommRing (i : Fin 3) : CommRing (chart i) := inferInstance
local instance originTensorChartSemiring (i : Fin 3) : Semiring (chart i) :=
  (originTensorChartCommRing i).toSemiring
local instance originTensorPlaneCommRing (i : Fin 3) : CommRing (planeChart i) := inferInstance
local instance originTensorPlaneSemiring (i : Fin 3) : Semiring (planeChart i) :=
  (originTensorPlaneCommRing i).toSemiring

local instance originScalar : Algebra S ℂ := MvPolynomial.constantCoeff.toAlgebra
local instance originPlane (i : Fin 3) : Algebra S (planeChart i) :=
  ((algebraMap ℂ (planeChart i)).comp MvPolynomial.constantCoeff).toAlgebra
local instance originChart (i : Fin 3) : Algebra S (chart i) := (baseMap i).toAlgebra
def originScalarHom (i : Fin 3) : ℂ →ₐ[S] planeChart i :=
  { algebraMap ℂ (planeChart i) with commutes' := fun _ => rfl }

abbrev originTensor (i : Fin 3) := ℂ ⊗[S] chart i
local instance originTensorCommRing (i : Fin 3) : CommRing (originTensor i) := inferInstance
local instance originTensorSemiring (i : Fin 3) : Semiring (originTensor i) :=
  (originTensorCommRing i).toSemiring

def zeroEvaluationAlg (i : Fin 3) : chart i →ₐ[S] planeChart i :=
  { zeroEvaluation i with
    commutes' := fun a => RingHom.congr_fun (zeroEvaluation_base i) a }

def originTensorMap (i : Fin 3) : originTensor i →ₐ[S] planeChart i :=
  Algebra.TensorProduct.lift (originScalarHom i)
    (zeroEvaluationAlg i) (fun _ _ => Commute.all _ _)

def originTensorInverse (i : Fin 3) : planeChart i →+* originTensor i :=
  Algebra.TensorProduct.includeRight.toRingHom.comp (directionMap i)

lemma originTensor_base (i : Fin 3) (a : S) :
    (1 : ℂ) ⊗ₜ[S] baseMap i a = MvPolynomial.constantCoeff a ⊗ₜ[S] (1 : chart i) := by
  exact (RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap a).symm

lemma originTensor_fiber (i : Fin 3) :
    (1 : ℂ) ⊗ₜ[S] baseMap i (MvPolynomial.X i) = (0 : originTensor i) := by
  rw [originTensor_base, MvPolynomial.constantCoeff_X, zero_tmul]

lemma originTensorInverse_scalar (i : Fin 3) (a : ℂ) :
    originTensorInverse i (algebraMap ℂ (planeChart i) a) = a ⊗ₜ[S] (1 : chart i) := by
  change (1 : ℂ) ⊗ₜ[S] directionMap i (algebraMap ℂ (planeChart i) a) = _
  rw [directionMap_scalar, originTensor_base, MvPolynomial.constantCoeff_C]

lemma originTensorInverse_zeroEvaluation (i : Fin 3) (e : chart i) :
    originTensorInverse i (zeroEvaluation i e) = (1 : ℂ) ⊗ₜ[S] e := by
  have he : ((originTensorInverse i).comp (zeroEvaluation i)).comp
      (planePolynomialEquiv i).toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (planePolynomialEquiv i).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change originTensorInverse i (zeroEvaluation i (planePolynomialEquiv i (C a))) =
        (1 : ℂ) ⊗ₜ[S] planePolynomialEquiv i (C a)
      rw [planePolynomialEquiv_C, zeroEvaluation_direction]
      rfl
    · change originTensorInverse i (zeroEvaluation i (planePolynomialEquiv i X)) =
        (1 : ℂ) ⊗ₜ[S] planePolynomialEquiv i X
      rw [planePolynomialEquiv_X, zeroEvaluation_fiber, map_zero]
      exact (originTensor_fiber i).symm
  have hh := RingHom.congr_fun he ((planePolynomialEquiv i).symm e)
  change originTensorInverse i (zeroEvaluation i
    (planePolynomialEquiv i ((planePolynomialEquiv i).symm e))) =
      (1 : ℂ) ⊗ₜ[S] (planePolynomialEquiv i ((planePolynomialEquiv i).symm e)) at hh
  simpa only [AlgEquiv.apply_symm_apply] using hh

lemma originTensorMap_tmul (i : Fin 3) (a : ℂ) (e : chart i) :
    originTensorMap i (a ⊗ₜ[S] e) = algebraMap ℂ (planeChart i) a * zeroEvaluation i e := by
  simp only [originTensorMap, Algebra.TensorProduct.lift_tmul]
  rfl

lemma originTensor_left_inverse (i : Fin 3) (x : originTensor i) :
    originTensorInverse i (originTensorMap i x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    rw [originTensorMap_tmul, map_mul, originTensorInverse_scalar,
      originTensorInverse_zeroEvaluation, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]

lemma originTensor_right_inverse (i : Fin 3) (a : planeChart i) :
    originTensorMap i (originTensorInverse i a) = a := by
  change originTensorMap i ((1 : ℂ) ⊗ₜ[S] directionMap i a) = a
  rw [originTensorMap_tmul, map_one, one_mul, zeroEvaluation_direction]

/-- Closed fiber chart with its actual structural maps, not just an
existential abstract isomorphism of rings. -/
def originTensorEquiv (i : Fin 3) : originTensor i ≃+* planeChart i :=
  { (originTensorMap i).toRingHom with
    invFun := originTensorInverse i
    left_inv := originTensor_left_inverse i
    right_inv := originTensor_right_inverse i }

@[simp] lemma originTensorEquiv_direction (i : Fin 3) (a : planeChart i) :
    originTensorEquiv i ((1 : ℂ) ⊗ₜ[S] directionMap i a) = a :=
  originTensor_right_inverse i a

end SourcePullbackChart

end


/-! The closed fiber of the literal Rees blowup of S at the origin is the
projective plane, built from its affine tensor charts. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel
attribute [local instance] originScalar originChart
  originTensorChartCommRing originTensorChartSemiring originTensorPlaneCommRing
  originTensorPlaneSemiring originTensorCommRing originTensorSemiring

abbrev originPoint : Spec (.of ℂ) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff : S →+* ℂ))
abbrev originFiber : Scheme := pullback originPoint blowdown

def fiberDirection : originFiber ⟶ ExplicitCone.plane := pullback.snd _ _ ≫ direction

def originFiberIota (i : Fin 3) : Spec (.of (originTensor i)) ⟶ originFiber :=
  (pullbackSpecIso S ℂ (chart i)).inv ≫
    pullback.map originPoint (Spec.map (CommRingCat.ofHom (baseMap i))) originPoint blowdown
      (𝟙 _) (blowupIota i) (𝟙 _) (by simp) (by simp [blowupIota_blowdown])

instance (i : Fin 3) : IsOpenImmersion (originFiberIota i) := by
  unfold originFiberIota
  infer_instance

@[reassoc] lemma originFiberIota_fst (i : Fin 3) :
    originFiberIota i ≫ pullback.fst originPoint blowdown =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        ℂ →+* originTensor i)) := by
  simp only [originFiberIota, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
  exact pullbackSpecIso_inv_fst S ℂ (chart i)

@[reassoc] lemma originFiberIota_snd (i : Fin 3) :
    originFiberIota i ≫ pullback.snd originPoint blowdown =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        chart i →+* originTensor i)) ≫ blowupIota i := by
  simp only [originFiberIota, Category.assoc, pullback.map, pullback.lift_snd]
  rw [← Category.assoc]
  exact congrArg (fun u => u ≫ blowupIota i) (pullbackSpecIso_inv_snd S ℂ (chart i))

@[reassoc] lemma originFiberIota_direction (i : Fin 3) :
    originFiberIota i ≫ fiberDirection =
      Spec.map (CommRingCat.ofHom (originTensorInverse i)) ≫ planeIota i := by
  rw [fiberDirection, originFiberIota_snd_assoc, blowup_chart_square,
    ← Category.assoc, ← Spec.map_comp]
  rfl

lemma originFiberIota_isPullback (i : Fin 3) :
    IsPullback (originFiberIota i)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        chart i →+* originTensor i)))
      (pullback.snd originPoint blowdown) (blowupIota i) := by
  have ht : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : ℂ →+* originTensor i)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : chart i →+* originTensor i)))
      originPoint (Spec.map (CommRingCat.ofHom (baseMap i))) := by
    apply (IsPullback.of_hasPullback originPoint (Spec.map (CommRingCat.ofHom (baseMap i)))).of_iso'
      (pullbackSpecIso S ℂ (chart i)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      exact pullbackSpecIso_inv_fst S ℂ (chart i)
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      exact pullbackSpecIso_inv_snd S ℂ (chart i)
    · simp
    · simp
  have hh : IsPullback (originFiberIota i ≫ pullback.fst originPoint blowdown)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : chart i →+* originTensor i)))
      originPoint (blowupIota i ≫ blowdown) := by
    rw [originFiberIota_fst, blowupIota_blowdown]
    exact ht
  exact hh.of_right (originFiberIota_snd i) (IsPullback.of_hasPullback originPoint blowdown)

lemma originFiberIota_opensRange (i : Fin 3) :
    (originFiberIota i).opensRange =
      (pullback.snd originPoint blowdown) ⁻¹ᵁ (blowupIota i).opensRange := by
  have hh := (Scheme.Hom.opensRange_comp_of_isIso
    (originFiberIota_isPullback i).isoPullback.hom
    (pullback.fst (pullback.snd originPoint blowdown) (blowupIota i))).trans
      (Scheme.Hom.opensRange_pullbackFst (blowupIota i) (pullback.snd originPoint blowdown))
  simpa only [(originFiberIota_isPullback i).isoPullback_hom_fst] using hh

lemma fiberDirection_restrict_isIso (i : Fin 3) :
    IsIso (fiberDirection ∣_ (planeIota i).opensRange) := by
  have : IsIso (CommRingCat.ofHom (originTensorInverse i)) :=
    inferInstanceAs (IsIso (originTensorEquiv i).symm.toCommRingCatIso.hom)
  have : IsIso ((originFiberIota i ≫ fiberDirection) ∣_ (planeIota i).opensRange) := by
    rw [originFiberIota_direction]
    apply SchemeRestrictionImage.openImmersion_restrict_isIso
    rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply SchemeRestrictionImage.isIso_of_chart (originFiberIota i) fiberDirection
  rw [originFiberIota_opensRange]
  change (pullback.snd originPoint blowdown) ⁻¹ᵁ
    (direction ⁻¹ᵁ (planeIota i).opensRange) ≤ _
  apply (pullback.snd originPoint blowdown).preimage_mono
  dsimp only [planeIota, blowupIota]
  erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  exact le_refl _

instance fiberDirection_isIso : IsIso fiberDirection := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i : Fin 3 => (planeIota i).opensRange) planeCover.iSup_opensRange
  exact fiberDirection_restrict_isIso

def originFiberIso : originFiber ≅ ExplicitCone.plane := asIso fiberDirection

end SourcePullbackChart

end

noncomputable section
namespace ExplicitCone
def projectiveCompletedParameterHom :
    MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] completedRing :=
  SectionGenerated.substHom pieces projectiveParameter (fun _ => 1)
    (fun _ => one_ne_zero) projectiveParameter_mem
end ExplicitCone

/-! Completion as a finite module agrees with completion at the extended ideal. -/
open Submodule
namespace ConeCompletion
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (I : Ideal R)

private lemma pow_smul_eq_restrict (n : ℕ) :
    I ^ n • (⊤ : Submodule R B) =
      (((I.map (algebraMap R B)) ^ n • (⊤ : Ideal B)).restrictScalars R) := by
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.smul_top_eq_map, Ideal.map_pow]

def quotientScalarEquiv (n : ℕ) :
    (B ⧸ (I ^ n • (⊤ : Submodule R B))) ≃ₗ[R]
      B ⧸ ((I.map (algebraMap R B)) ^ n • (⊤ : Ideal B)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_eq_restrict I n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp] lemma quotientScalarEquiv_mk (n : ℕ) (b : B) :
    quotientScalarEquiv I n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := by
  simp only [quotientScalarEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]

@[simp] lemma quotientScalarEquiv_symm_mk (n : ℕ) (b : B) :
    (quotientScalarEquiv I n).symm (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk b := by
  apply (quotientScalarEquiv I n).injective
  rw [LinearEquiv.apply_symm_apply, quotientScalarEquiv_mk]

lemma quotientScalarEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : B ⧸ (I ^ n • (⊤ : Submodule R B))) :
    AdicCompletion.transitionMap (I.map (algebraMap R B)) B h
        (quotientScalarEquiv I n x) =
      quotientScalarEquiv I m (AdicCompletion.transitionMap I B h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ b =>
    rw [quotientScalarEquiv_mk]
    exact (quotientScalarEquiv_mk I m b).symm

lemma quotientScalarEquiv_symm_transition {m n : ℕ} (h : m ≤ n)
    (x : B ⧸ ((I.map (algebraMap R B)) ^ n • (⊤ : Ideal B))) :
    AdicCompletion.transitionMap I B h ((quotientScalarEquiv I n).symm x) =
      (quotientScalarEquiv I m).symm
        (AdicCompletion.transitionMap (I.map (algebraMap R B)) B h x) := by
  apply (quotientScalarEquiv I m).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [← quotientScalarEquiv_transition, LinearEquiv.apply_symm_apply]

def scalarEquiv : AdicCompletion I B ≃ₗ[R]
    AdicCompletion (I.map (algebraMap R B)) B where
  toFun x := ⟨fun n => quotientScalarEquiv I n (x.val n), fun h => by
    rw [quotientScalarEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (quotientScalarEquiv I n).symm (x.val n), fun h => by
    rw [quotientScalarEquiv_symm_transition, x.property h]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (quotientScalarEquiv I n).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (quotientScalarEquiv I n).apply_symm_apply _
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (quotientScalarEquiv I n) _ _
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (quotientScalarEquiv I n).map_smul r _

@[simp] lemma scalarEquiv_of (b : B) :
    scalarEquiv I (AdicCompletion.of I B b) =
      AdicCompletion.of (I.map (algebraMap R B)) B b := by
  apply Subtype.ext
  funext n
  exact quotientScalarEquiv_mk I n b

@[simp] lemma scalarEquiv_symm_of (b : B) :
    (scalarEquiv I).symm (AdicCompletion.of (I.map (algebraMap R B)) B b) =
      AdicCompletion.of I B b := by
  apply (scalarEquiv I).injective
  simp

end ConeCompletion


/-! Necessary uniqueness statement for the canonical cone base-change map.
R-linearity forces adic continuity, so no continuity hypothesis is smuggled in. -/
open Submodule
namespace ConeCompletion
variable {R M N : Type*} [CommRing R] (I : Ideal R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma linearMap_ext_on_base (hI : I.FG) [IsHausdorff I N]
    {f g : AdicCompletion I M →ₗ[R] N}
    (hfg : ∀ b : M, f (AdicCompletion.of I M b) = g (AdicCompletion.of I M b)) :
    f = g := by
  apply LinearMap.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R M))
    (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M b ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change AdicCompletion.eval I M n (x - AdicCompletion.of I M b) = 0
    rw [map_sub, AdicCompletion.eval_of, hb, sub_self]
  have hf := Submodule.smul_top_le_comap_smul_top (I ^ n) (f - g) hx
  rw [Submodule.mem_comap, LinearMap.sub_apply, map_sub, map_sub, hfg b] at hf
  rw [SModEq.sub_mem]
  simpa only [sub_sub_sub_cancel_right] using hf

end ConeCompletion


/-! Maps between the adic completions induced by the cone parameters. -/
namespace ConeCompletion
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (I : Ideal R) (J : Ideal B)

lemma eval_compatible {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  refine AdicCompletion.induction_on I R (p := fun y =>
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y) x ?_
  intro f
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (f.val n) = Ideal.Quotient.mk (I ^ m) (f.val m)
  exact AdicCompletion.Ideal.mk_eq_mk I h f

variable (hIJ : I.map (algebraMap R B) ≤ J)

include hIJ in
lemma pow_le_comap (n : ℕ) : I ^ n ≤ (J ^ n).comap (algebraMap R B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact pow_le_pow_left' hIJ n

def algebraLevelMap (n : ℕ) : AdicCompletion I R →ₐ[R] B ⧸ J ^ n :=
  (Ideal.quotientMapₐ (J ^ n) (Algebra.ofId R B) (pow_le_comap I J hIJ n)).comp
    (AdicCompletion.evalₐ I n)

@[simp] lemma algebraLevelMap_of (n : ℕ) (r : R) :
    algebraLevelMap I J hIJ n (AdicCompletion.of I R r) =
      algebraMap R (B ⧸ J ^ n) r := by
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using
    (algebraLevelMap I J hIJ n).commutes r

lemma algebraLevelMap_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp
      (algebraLevelMap I J hIJ n) = algebraLevelMap I J hIJ m := by
  apply AlgHom.ext
  intro x
  dsimp only [algebraLevelMap, AlgHom.comp_apply]
  rw [← eval_compatible I h x]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  rfl

def completionMap : AdicCompletion I R →ₐ[R] AdicCompletion J B :=
  AdicCompletion.liftAlgHom J (algebraLevelMap I J hIJ)
    (fun h => algebraLevelMap_compatible I J hIJ h)

@[simp] lemma eval_completionMap (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionMap I J hIJ x) =
      algebraLevelMap I J hIJ n x :=
  AdicCompletion.evalₐ_liftAlgHom _ _ _ _ _

@[simp] lemma completionMap_of (r : R) :
    completionMap I J hIJ (AdicCompletion.of I R r) =
      AdicCompletion.of J B (algebraMap R B r) := by
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using (completionMap I J hIJ).commutes r

end ConeCompletion


/-! A finite-module scalar extension of a ring is its completion at the extended ideal. -/
open TensorProduct
namespace ConeCompletion
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (I : Ideal R)

private abbrev J : Ideal B := I.map (algebraMap R B)

def tensorMap : AdicCompletion I R ⊗[R] B →ₐ[R] AdicCompletion (J (B := B) I) B :=
  Algebra.TensorProduct.lift (completionMap I (J (B := B) I) le_rfl)
    (IsScalarTower.toAlgHom R B (AdicCompletion (J (B := B) I) B)) (fun _ _ => .all _ _)

@[simp] lemma tensorMap_tmul (a : AdicCompletion I R) (b : B) :
    tensorMap I (a ⊗ₜ[R] b) =
      completionMap I (J (B := B) I) le_rfl a * AdicCompletion.of (J (B := B) I) B b := by
  rfl

lemma tensorMap_linear_eq (hI : I.FG) :
    (tensorMap I (B := B)).toLinearMap =
      (scalarEquiv I).toLinearMap.comp ((AdicCompletion.ofTensorProduct I B).restrictScalars R) := by
  let : IsHausdorff I (AdicCompletion (J (B := B) I) B) :=
    (IsHausdorff.map_algebraMap_iff (S := B)).mp inferInstance
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  let t := (TensorProduct.mk R (AdicCompletion I R) B).flip b
  have h := linearMap_ext_on_base I hI
    (f := (tensorMap I).toLinearMap.comp t)
    (g := ((scalarEquiv I).toLinearMap.comp
      ((AdicCompletion.ofTensorProduct I B).restrictScalars R)).comp t) (by
        intro r
        change tensorMap I ((AdicCompletion.of I R r) ⊗ₜ[R] b) =
          scalarEquiv I ((AdicCompletion.of I R r) • AdicCompletion.of I B b)
        rw [tensorMap_tmul, completionMap_of]
        have ha : AdicCompletion.of I R r = algebraMap R (AdicCompletion I R) r := by
          simp [AdicCompletion.algebraMap_apply]
        rw [ha, IsScalarTower.algebraMap_smul,
          ← (AdicCompletion.of I B).map_smul, scalarEquiv_of]
        change algebraMap B (AdicCompletion (J (B := B) I) B) (algebraMap R B r) *
          algebraMap B (AdicCompletion (J (B := B) I) B) b =
          algebraMap B (AdicCompletion (J (B := B) I) B) (r • b)
        rw [← map_mul, Algebra.smul_def])
  exact LinearMap.congr_fun h a

lemma tensorMap_bijective [IsNoetherianRing R] [Module.Finite R B] :
    Function.Bijective (tensorMap I (B := B)) := by
  have h := tensorMap_linear_eq (B := B) I (IsNoetherian.noetherian I)
  change Function.Bijective (tensorMap I (B := B)).toLinearMap
  rw [h]
  exact (scalarEquiv I).bijective.comp
    (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I B)

def tensorEquiv [IsNoetherianRing R] [Module.Finite R B] :
    AdicCompletion I R ⊗[R] B ≃ₐ[R] AdicCompletion (J (B := B) I) B :=
  AlgEquiv.ofBijective (tensorMap I) (tensorMap_bijective I)

end ConeCompletion


/-! Cofinal adic filtrations give canonically identical completed rings. -/
namespace ConeCompletion
variable {R : Type*} [CommRing R]
variable (I J : Ideal R) (d : ℕ) (h : I ^ d ≤ J)

include h in
lemma pow_mul_le (n : ℕ) : I ^ (d * n) ≤ J ^ n := by
  rw [pow_mul]
  exact pow_le_pow_left' h n

def powerLevelMap (n : ℕ) : AdicCompletion I R →ₐ[R] R ⧸ J ^ n :=
  (Ideal.Quotient.factorₐ R (pow_mul_le I J d h n)).comp (AdicCompletion.evalₐ I (d * n))

lemma powerLevelMap_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
      (powerLevelMap I J d h n) = powerLevelMap I J d h m := by
  apply AlgHom.ext
  intro x
  dsimp only [powerLevelMap, AlgHom.comp_apply]
  rw [← eval_compatible I (Nat.mul_le_mul_left d hmn) x]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (d * n) x)
  rw [← hr]
  rfl

def powerMap : AdicCompletion I R →ₐ[R] AdicCompletion J R :=
  AdicCompletion.liftAlgHom J (powerLevelMap I J d h)
    (fun hmn => powerLevelMap_compatible I J d h hmn)

@[simp] lemma powerMap_of (r : R) :
    powerMap I J d h (AdicCompletion.of I R r) = AdicCompletion.of J R r := by
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using
    (powerMap I J d h).commutes r

lemma algHom_ext_on_base (hI : I.FG) {A : Type*} [CommRing A] [Algebra R A]
    [IsHausdorff I A] (f g : AdicCompletion I R →ₐ[R] A) : f = g := by
  apply AlgHom.toLinearMap_injective
  apply linearMap_ext_on_base I hI
  intro r
  have hr : AdicCompletion.of I R r = algebraMap R (AdicCompletion I R) r := by
    simp [AdicCompletion.algebraMap_apply]
  simp only [AlgHom.toLinearMap_apply, hr, AlgHom.commutes]

def cofinalEquiv (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J) (e : ℕ) (hJI : J ^ e ≤ I) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J R := by
  let f := powerMap I J 1 (by simpa using hIJ)
  let g := powerMap J I e hJI
  have hgf : g.comp f = AlgHom.id R (AdicCompletion I R) := algHom_ext_on_base I hI _ _
  have hfg : f.comp g = AlgHom.id R (AdicCompletion J R) := algHom_ext_on_base J hJ _ _
  exact { f with
    invFun := g
    left_inv := fun x => AlgHom.congr_fun hgf x
    right_inv := fun x => AlgHom.congr_fun hfg x }

@[simp] lemma cofinalEquiv_of (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (e : ℕ) (hJI : J ^ e ≤ I) (r : R) :
    cofinalEquiv I J hI hJ hIJ e hJI (AdicCompletion.of I R r) =
      AdicCompletion.of J R r :=
  powerMap_of I J 1 (by simpa using hIJ) r

end ConeCompletion


/-! Degree-one parameters identify completion with scalar extension. -/
open _root_.Polynomial _root_.OAI.Polynomial
namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma scale_mem (a : k) (p : polynomials T) :
    GradedNormalization.scale a p.val ∈ polynomials T := by
  rw [GradedNormalization.scale_eq_sum]
  apply Subalgebra.sum_mem
  intro i hi
  apply Subalgebra.smul_mem
  exact (monomial_mem_polynomials T _ _).mpr (p.property i)

def scaleHom (a : k) : polynomials T →ₐ[k] polynomials T :=
  ((GradedNormalization.scale a).comp (polynomials T).val).codRestrict
    (polynomials T) (scale_mem T a)

lemma scaleHom_monomial (a : k) (n : ℕ) (c : K) (hc : c ∈ T n) :
    scaleHom T a (⟨monomial n c, (monomial_mem_polynomials T n c).mpr hc⟩ : polynomials T) =
      a ^ n • (⟨monomial n c, (monomial_mem_polynomials T n c).mpr hc⟩ : polynomials T) := by
  apply Subtype.ext
  exact GradedNormalization.scale_monomial a n c

lemma monomial_mem_of_scale_stable [CharZero k] (J : Ideal (polynomials T))
    (hJ : ∀ (a : k) (p : polynomials T), p ∈ J → scaleHom T a p ∈ J)
    (p : polynomials T) (hp : p ∈ J) (n : ℕ) :
    (⟨monomial n (p.val.coeff n),
      (monomial_mem_polynomials T n _).mpr (p.property n)⟩ : polynomials T) ∈ J := by
  have h := GradedNormalization.monomial_mem_of_scale_mem
    ((J.restrictScalars k).map (polynomials T).val.toLinearMap) p.val (fun a => by
      exact ⟨scaleHom T a p, hJ a p hp, rfl⟩) n
  obtain ⟨q, hq, heq⟩ := h
  have : q = (⟨monomial n (p.val.coeff n),
      (monomial_mem_polynomials T n _).mpr (p.property n)⟩ : polynomials T) :=
    Subtype.ext heq
  rwa [← this]

lemma scaleHom_parameter {σ : Type} [Fintype σ] (w : σ → K)
    (hw : ∀ i, w i ∈ T 1) (a : k) (i : σ) :
    scaleHom T a (linearPolynomialMap T w hw (MvPolynomial.X i)) =
      a • linearPolynomialMap T w hw (MvPolynomial.X i) := by
  simp only [linearPolynomialMap, MvPolynomial.aeval_X]
  simpa only [pow_one] using scaleHom_monomial T a 1 (w i) (hw i)

lemma scale_stable_linearIdeal {σ : Type} [Fintype σ] (w : σ → K)
    (hw : ∀ i, w i ∈ T 1) :
    let J := Ideal.span (Set.range (fun i => linearPolynomialMap T w hw (MvPolynomial.X i)))
    ∀ (a : k) (p : polynomials T), p ∈ J → scaleHom T a p ∈ J := by
  intro J a p hp
  have h : J.map (scaleHom T a).toRingHom ≤ J := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro q ⟨p, ⟨i, rfl⟩, rfl⟩
    change scaleHom T a (linearPolynomialMap T w hw (MvPolynomial.X i)) ∈ J
    rw [scaleHom_parameter]
    exact (J.restrictScalars k).smul_mem a (Ideal.subset_span ⟨i, rfl⟩)
  exact h (Ideal.mem_map_of_mem _ hp)

def cofinalHomogeneousPart (n : ℕ) : polynomials T →ₗ[k] polynomials T where
  toFun p := ⟨monomial n (p.val.coeff n),
    (monomial_mem_polynomials T n _).mpr (p.property n)⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, coeff_add, map_add]
  map_smul' c p := by
    apply Subtype.ext
    simp only [Subalgebra.coe_smul, coeff_smul, smul_monomial, RingHom.id_apply]

lemma cofinalHomogeneousPart_sum (p : polynomials T) :
    ∑ n ∈ Finset.range (p.val.natDegree + 1), cofinalHomogeneousPart T n p = p := by
  apply Subtype.ext
  change (polynomials T).val (∑ n ∈ Finset.range (p.val.natDegree + 1),
    cofinalHomogeneousPart T n p) = p.val
  rw [map_sum]
  exact p.val.as_sum_range.symm

lemma cofinalHomogeneousPart_eq_zero_of_degree_lt (p : polynomials T) {n : ℕ}
    (hn : p.val.natDegree < n) : cofinalHomogeneousPart T n p = 0 := by
  apply Subtype.ext
  change monomial n (p.val.coeff n) = 0
  simp [coeff_eq_zero_of_natDegree_lt hn]

lemma finite_quotient_degreeIdeal_le [CharZero k] (J : Ideal (polynomials T))
    [Module.Finite k (polynomials T ⧸ J)]
    (hJ : ∀ (a : k) (p : polynomials T), p ∈ J → scaleHom T a p ∈ J) :
    ∃ D : ℕ, 0 < D ∧ degreeIdeal T D ≤ J := by
  classical
  let : Module.Free k (polynomials T ⧸ J) := Module.Free.of_divisionRing k _
  let basis := Module.finBasis k (polynomials T ⧸ J)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (basis i)
  let D := (Finset.univ.sup (fun i => (b i).val.natDegree)) + 1
  refine ⟨D, Nat.succ_pos _, ?_⟩
  have hpart : ∀ (p : polynomials T) (n : ℕ), D ≤ n → cofinalHomogeneousPart T n p ∈ J := by
    intro p n hn
    let c := basis.repr (Ideal.Quotient.mk J p)
    let q := ∑ i, c i • b i
    have heq : Ideal.Quotient.mk J q = Ideal.Quotient.mk J p := by
      change Ideal.Quotient.mkₐ k J q = _
      dsimp only [q]
      simp only [map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk, hb]
      exact basis.sum_repr _
    have hpq : p - q ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem p q).mp heq.symm
    have hq : cofinalHomogeneousPart T n q = 0 := by
      dsimp only [q]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_smul, cofinalHomogeneousPart_eq_zero_of_degree_lt]
      · exact smul_zero _
      · have hi' : (b i).val.natDegree ≤ Finset.univ.sup (fun j => (b j).val.natDegree) :=
          Finset.le_sup (f := fun j => (b j).val.natDegree) (Finset.mem_univ i)
        exact (Nat.lt_succ_of_le hi').trans_le hn
    have hm := monomial_mem_of_scale_stable T J hJ (p - q) hpq n
    change cofinalHomogeneousPart T n (p - q) ∈ J at hm
    simpa only [map_sub, hq, sub_zero] using hm
  intro p hp
  rw [← cofinalHomogeneousPart_sum T p]
  apply J.sum_mem
  intro n hn
  by_cases hDn : D ≤ n
  · exact hpart p n hDn
  · have hc := (mem_degreeIdeal T D p).mp hp n (Nat.lt_of_not_ge hDn)
    have hz : cofinalHomogeneousPart T n p = 0 := by
      apply Subtype.ext
      change monomial n (p.val.coeff n) = 0
      simp [hc]
    rw [hz]
    exact J.zero_mem

lemma linear_parameter_cofinal [CharZero k] [IsAlgClosed k] {σ : Type} [Fintype σ]
    (w : σ → K) (hw : ∀ i, w i ∈ T 1)
    (hfin : (linearPolynomialMap T w hw).Finite) :
    let J := Ideal.span (Set.range (fun i => linearPolynomialMap T w hw (MvPolynomial.X i)))
    ∃ D : ℕ, 0 < D ∧ degreeIdeal T 1 ^ D ≤ J := by
  intro J
  have : Module.Finite k (polynomials T ⧸ J) :=
    SmallCM.finite_polynomial_origin_fiber _ hfin
  obtain ⟨D, hD, hDJ⟩ := finite_quotient_degreeIdeal_le T J (scale_stable_linearIdeal T w hw)
  exact ⟨D, hD, (degreeIdeal_one_pow_le T D).trans hDJ⟩

end SectionCompletion


/-! Necessary canonical source identity, the manuscript, lines 221–239. -/
open TensorProduct
namespace SectionCompletion
variable {k K σ : Type} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma exists_augmentationCompletionEquiv [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    ∃ e : series T ≃ₐ[k] AdicCompletion (degreeIdeal T 1) (polynomials T),
      ∀ b : polynomials T, e (polynomialToSeries T b) =
        AdicCompletion.of (degreeIdeal T 1) (polynomials T) b := by
  classical
  obtain ⟨τ, hτ, v, d, hd, hv, hgen⟩ := finite_positive_presentation T hzero
  let := hτ
  let D : ℕ := Finset.univ.sup d + 1
  have hD : 0 < D := Nat.succ_pos _
  have hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n :=
    degreeIdeal_cofinal T v d hd hv hgen D hD
      (fun i => (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
  exact ⟨completionEquiv T D hD hc, fun b => completionEquiv_polynomial T D hD hc b⟩

lemma polynomial_subst_square (w : σ → K) (hw : ∀ i, w i ∈ T 1) :
    (polynomialToSeries T).comp (linearPolynomialMap T w hw) =
      (SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw).comp
        (MvPolynomial.aeval MvPowerSeries.X) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  exact polynomial_subst_X T w hw i

omit [Fintype σ] in
lemma map_vars_eq_linearIdeal (w : σ → K) (hw : ∀ i, w i ∈ T 1) :
    (MvPolynomial.idealOfVars σ k).map (linearPolynomialMap T w hw).toRingHom =
      Ideal.span (Set.range (fun i => linearPolynomialMap T w hw (MvPolynomial.X i))) := by
  simp only [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  rfl

omit [Fintype σ] in
lemma map_vars_le_degreeIdeal (w : σ → K) (hw : ∀ i, w i ∈ T 1) :
    (MvPolynomial.idealOfVars σ k).map (linearPolynomialMap T w hw).toRingHom ≤
      degreeIdeal T 1 := by
  rw [map_vars_eq_linearIdeal]
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  simp only [linearPolynomialMap, MvPolynomial.aeval_X]
  exact monomial_mem_degreeIdeal_one T one_ne_zero _ (hw i)

omit [Fintype σ] in
lemma polynomial_algebraMap_eq_aeval (p : MvPolynomial σ k) :
    algebraMap (MvPolynomial σ k) (MvPowerSeries σ k) p =
      MvPolynomial.aeval MvPowerSeries.X p := by
  have h : (MvPolynomial.coeToMvPowerSeries.algHom k :
      MvPolynomial σ k →ₐ[k] MvPowerSeries σ k) = MvPolynomial.aeval MvPowerSeries.X := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply]
  exact AlgHom.congr_fun h p

/-- Canonical base change at the very same degree-one sections. -/
theorem exists_canonicalTensorEquiv [CharZero k] [IsAlgClosed k]
    [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    (w : σ → K) (hw : ∀ i, w i ∈ T 1)
    (hfin : (linearPolynomialMap T w hw).Finite) :
    letI : Algebra (MvPolynomial σ k) (polynomials T) :=
      (linearPolynomialMap T w hw).toRingHom.toAlgebra
    letI : IsScalarTower k (MvPolynomial σ k) (polynomials T) :=
      IsScalarTower.of_algebraMap_eq (fun a => ((linearPolynomialMap T w hw).commutes a).symm)
    ∃ e : (MvPowerSeries σ k ⊗[MvPolynomial σ k] polynomials T) ≃ₐ[k] series T,
      ∀ (a : MvPowerSeries σ k) (b : polynomials T),
        e (a ⊗ₜ[MvPolynomial σ k] b) =
          SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw a *
            polynomialToSeries T b := by
  classical
  let S := MvPolynomial σ k
  let B := polynomials T
  let I := MvPolynomial.idealOfVars σ k
  let f := linearPolynomialMap T w hw
  let : Algebra S B := f.toRingHom.toAlgebra
  let : IsScalarTower k S B :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : Module.Finite S B := hfin
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let J := I.map (algebraMap S B)
  let m := degreeIdeal T 1
  have hJm : J ≤ m := map_vars_le_degreeIdeal T w hw
  obtain ⟨d, hd, hmd⟩ := linear_parameter_cofinal T w hw hfin
  have hmd' : m ^ d ≤ J := by
    simpa only [m, J, I, S, B, RingHom.algebraMap_toAlgebra, f, map_vars_eq_linearIdeal] using hmd
  obtain ⟨eSeries, heSeries⟩ := exists_augmentationCompletionEquiv T hzero
  let ePower := MvPowerSeries.toAdicCompletionAlgEquiv σ k
  let eTensor := Algebra.TensorProduct.congr ePower (AlgEquiv.refl : B ≃ₐ[S] B)
  let eFinite := ConeCompletion.tensorEquiv (B := B) I
  let eCofinal := ConeCompletion.cofinalEquiv J m
    (IsNoetherian.noetherian J) (IsNoetherian.noetherian m) hJm d hmd'
  let e := (eTensor.restrictScalars k).trans ((eFinite.restrictScalars k).trans
    ((eCofinal.restrictScalars k).trans eSeries.symm))
  refine ⟨e, ?_⟩
  let g := SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw
  let F : AdicCompletion I S →ₐ[S] AdicCompletion m B :=
    (eCofinal.toAlgHom.restrictScalars S).comp (ConeCompletion.completionMap I J le_rfl)
  let Gk := (eSeries.toAlgHom.comp g).comp (ePower.symm.restrictScalars k).toAlgHom
  let G : AdicCompletion I S →ₐ[S] AdicCompletion m B :=
    { Gk.toRingHom with
      commutes' := fun p => by
        change eSeries (g (ePower.symm (algebraMap S (AdicCompletion I S) p))) =
          algebraMap S (AdicCompletion m B) p
        rw [ePower.symm.commutes]
        change eSeries (g (algebraMap (MvPolynomial σ k) (MvPowerSeries σ k) p)) = _
        rw [polynomial_algebraMap_eq_aeval]
        have hp := AlgHom.congr_fun (polynomial_subst_square T w hw) p
        change polynomialToSeries T (f p) = g (MvPolynomial.aeval MvPowerSeries.X p) at hp
        rw [← hp, heSeries]
        rfl }
  let : IsHausdorff I (AdicCompletion m B) := IsHausdorff.of_map (S := B) hJm
  have hFG : F = G := ConeCompletion.algHom_ext_on_base I (IsNoetherian.noetherian I) F G
  intro a b
  apply eSeries.injective
  change eSeries (eSeries.symm (eCofinal (eFinite (eTensor (a ⊗ₜ[S] b))))) =
    eSeries (g a * polynomialToSeries T b)
  rw [eSeries.apply_symm_apply, map_mul, heSeries]
  change eCofinal (ConeCompletion.completionMap I J le_rfl (ePower a) *
    AdicCompletion.of J B b) = eSeries (g a) * AdicCompletion.of m B b
  rw [map_mul]
  have hbC : eCofinal (AdicCompletion.of J B b) = AdicCompletion.of m B b := by
    simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] using
      eCofinal.commutes b
  rw [hbC]
  congr 1
  have h := AlgHom.congr_fun hFG (ePower a)
  change F (ePower a) = _
  rw [h]
  change eSeries (g (ePower.symm (ePower a))) = eSeries (g a)
  rw [ePower.symm_apply_apply]

end SectionCompletion


/-! Canonical completion and scalar-extension comparison for the normalized cone. -/
open TensorProduct
namespace ExplicitCone

/-- the manuscript, lines 221–239, on the exact normalized Kummer cone and the exact
projective Noether-normalization parameters, not an unrelated chosen map. -/
theorem exists_projectiveTensorEquiv :
    letI : Algebra (MvPolynomial (Fin 3) ℂ) (SectionCompletion.polynomials pieces) :=
      (SectionCompletion.linearPolynomialMap pieces projectiveParameter
        projectiveParameter_mem).toRingHom.toAlgebra
    letI : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
      projectiveCompletedParameterHom.toRingHom.toAlgebra
    ∃ e : (MvPowerSeries (Fin 3) ℂ ⊗[MvPolynomial (Fin 3) ℂ]
        SectionCompletion.polynomials pieces) ≃ₐ[MvPowerSeries (Fin 3) ℂ] completedRing,
      ∀ (a : MvPowerSeries (Fin 3) ℂ) (b : SectionCompletion.polynomials pieces),
        e (a ⊗ₜ[MvPolynomial (Fin 3) ℂ] b) =
          projectiveCompletedParameterHom a * SectionCompletion.polynomialToSeries pieces b := by
  let f := SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem
  let : Algebra (MvPolynomial (Fin 3) ℂ) (SectionCompletion.polynomials pieces) :=
    f.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 3) ℂ) (SectionCompletion.polynomials pieces) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
    projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
    GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale
  obtain ⟨e, he⟩ := SectionCompletion.exists_canonicalTensorEquiv pieces zero_piece
    projectiveParameter projectiveParameter_mem projectiveParameter_finite
  let eA : (MvPowerSeries (Fin 3) ℂ ⊗[MvPolynomial (Fin 3) ℂ]
      SectionCompletion.polynomials pieces) ≃ₐ[MvPowerSeries (Fin 3) ℂ] completedRing :=
    { e.toRingEquiv with
      commutes' := fun a => by
        change e (a ⊗ₜ[MvPolynomial (Fin 3) ℂ] 1) = projectiveCompletedParameterHom a
        simpa only [projectiveCompletedParameterHom, map_one, mul_one] using he a 1 }
  exact ⟨eA, he⟩

/-- Canonical algebra equivalence used to interpret the paper's tensor-product
cone as the already formalized degreewise completed ring. -/
def projectiveTensorEquiv :
    letI : Algebra (MvPolynomial (Fin 3) ℂ) (SectionCompletion.polynomials pieces) :=
      (SectionCompletion.linearPolynomialMap pieces projectiveParameter
        projectiveParameter_mem).toRingHom.toAlgebra
    letI : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
      projectiveCompletedParameterHom.toRingHom.toAlgebra
    (MvPowerSeries (Fin 3) ℂ ⊗[MvPolynomial (Fin 3) ℂ]
      SectionCompletion.polynomials pieces) ≃ₐ[MvPowerSeries (Fin 3) ℂ] completedRing :=
  exists_projectiveTensorEquiv.choose

theorem projectiveTensorEquiv_tmul :
    letI : Algebra (MvPolynomial (Fin 3) ℂ) (SectionCompletion.polynomials pieces) :=
      (SectionCompletion.linearPolynomialMap pieces projectiveParameter
        projectiveParameter_mem).toRingHom.toAlgebra
    letI : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
      projectiveCompletedParameterHom.toRingHom.toAlgebra
    ∀ (a : MvPowerSeries (Fin 3) ℂ) (b : SectionCompletion.polynomials pieces),
      projectiveTensorEquiv (a ⊗ₜ[MvPolynomial (Fin 3) ℂ] b) =
        projectiveCompletedParameterHom a * SectionCompletion.polynomialToSeries pieces b :=
  exists_projectiveTensorEquiv.choose_spec

end ExplicitCone

end

end OAI
