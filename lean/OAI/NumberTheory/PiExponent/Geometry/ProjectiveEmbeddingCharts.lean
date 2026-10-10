import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
variable {K σ R : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_evalAway_surjective (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
    (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
  have hC (r : K) : C r ∈ homogeneousSubmodule σ K (0 • 1) := by simp
  have hX (j : σ) : X j ∈ homogeneousSubmodule σ K (1 • 1) := by
    simpa using isHomogeneous_X K j
  let c : K →+* Away (homogeneousSubmodule σ K) (X i) :=
    (HomogeneousLocalization.fromZeroRingHom _ _).comp
      { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
        map_one' := Subtype.ext C_1
        map_mul' := fun _ _ => Subtype.ext C_mul
        map_zero' := Subtype.ext C_0
        map_add' := fun _ _ => Subtype.ext C_add }
  let b (j : σ) := Away.mk _ (isHomogeneous_X K i) 1 (X j) (hX j)
  have hc (r : K) : F (c r) = k r := by
    change F (Away.mk _ (isHomogeneous_X K i) 0 (C r) (hC r)) = k r
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 0 (C r) (hC r)
    simpa only [F, eval₂Hom_C, eval₂Hom_X', pow_zero, mul_one] using H
  have hb (j : σ) : F (b j) = a j := by
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j) (hX j)
    simpa only [F, b, eval₂Hom_X', hi, one_pow, mul_one] using H
  have H : F.comp (eval₂Hom c b) = eval₂Hom k a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval₂Hom_C] using hc r
    · intro j
      simpa only [RingHom.comp_apply, eval₂Hom_X'] using hb j
  intro r
  obtain ⟨p, hp⟩ := h r
  exact ⟨eval₂Hom c b p, (RingHom.congr_fun H p).trans hp⟩

lemma normalized_coordinates_closed {X : Scheme.{u}} [IsAffine X]
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (eval₂Hom k a)) :
    IsClosedImmersion (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (MvPolynomial.X i) (by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))
    (normalized_evalAway_surjective k a i hi h)
  infer_instance

end Projective

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {ι : Type u}

theorem closedImmersion_of_source_charts (f : X ⟶ Y) [UniversallyClosed f]
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (g : ∀ i, (U i).toScheme ⟶ (V i).toScheme)
    (hg : ∀ i, IsClosedImmersion (g i))
    (hcomm : ∀ i, (U i).ι ≫ f = g i ≫ (V i).ι)
    (hpre : ∀ i, f ⁻¹ᵁ V i = U i) : IsClosedImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hy : y ∈ U i := by
      rw [← hpre i]
      change f y ∈ V i
      rw [← hxy]
      change x ∈ f ⁻¹ᵁ V i
      rw [hpre]
      exact hi
    have he (z : (U i).toScheme) : (g i z).val = f z.val :=
      (congrArg (fun a : (U i).toScheme ⟶ Y => a z) (hcomm i)).symm
    have hz : g i ⟨x, hi⟩ = g i ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (he ⟨x, hi⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)
    have := (g i).isClosedEmbedding.injective hz
    exact congrArg Subtype.val this
  have hstalk : SurjectiveOnStalks f := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks)
      (X.openCoverOfIsOpenCover U hU)
    intro i
    change ι at i
    change SurjectiveOnStalks ((U i).ι ≫ f)
    rw [hcomm]
    have := hg i
    infer_instance
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous hinj f.isClosedMap⟩

end Geometry

namespace Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveConstants : K →+* homogeneousSubmodule σ K 0 where
  toFun r := ⟨C r, isHomogeneous_C _ _⟩
  map_one' := Subtype.ext C_1
  map_mul' _ _ := Subtype.ext C_mul
  map_zero' := Subtype.ext C_0
  map_add' _ _ := Subtype.ext C_add

def projectiveBase : Proj (homogeneousSubmodule σ K) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (projectiveConstants (σ := σ)))

lemma evalAway_constants_comp {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants_comp k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance projectiveBase_separated : IsSeparated (projectiveBase (K := K) (σ := σ)) := by
  unfold projectiveBase
  infer_instance

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end Projective

namespace Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

lemma finiteType_coordinates {K R : Type u} [CommRing K] [CommRing R]
    (k : K →+* R) (hk : k.FiniteType) :
    ∃ n : ℕ, ∃ a : Fin n → R, Function.Surjective (eval₂Hom k a) := by
  let := k.toAlgebra
  have : Algebra.FiniteType K R := hk
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K R)
  refine ⟨n, fun i => f (X i), ?_⟩
  have heq : eval₂Hom k (fun i => f (X i)) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (eval₂Hom_C _ _ _).trans (f.commutes c).symm
    · intro i
      exact eval₂Hom_X' _ _ _
  rw [heq]
  exact hf

theorem affine_coordinate_generators {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] :
    ∃ n : ℕ, ∃ a : Fin n → Γ(X, ⊤), Function.Surjective
      (eval₂Hom (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) a) := by
  have hp : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  exact finiteType_coordinates _ (hp.comp he)

end Geometry

end PiExponentSeshadri

end

end OAI
