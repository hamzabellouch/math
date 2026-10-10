import OAI.AlgebraicGeometry.SurfaceCones.AffineCanonicalCoordinates
import OAI.AlgebraicGeometry.SurfaceCones.SurfaceSmooth
import OAI.AlgebraicGeometry.SurfaceCones.ExteriorSheaf

namespace OAI

/-! Transport of determinant images under function-field automorphisms and compatible affine-ring isomorphisms. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {A B : Subalgebra k F} (σ : F ≃ₐ[k] F) (e : A ≃ₐ[k] B)
  (he : ∀ a : A, (e a : F) = σ (a : F))

local instance : RingHomSurjective e.toRingHom := ⟨e.surjective⟩

def rationalExteriorLinear :
    ExteriorAlgebra F Ω[F⁄k] →ₛₗ[e.toRingHom] ExteriorAlgebra F Ω[F⁄k] where
  toFun := exteriorFunctor σ.toAlgHom
  map_add' := by intro x y; exact map_add _ _ _
  map_smul' := by
    intro a v
    rw [← IsScalarTower.algebraMap_smul F a v, exteriorFunctor_smul]
    change σ (a : F) • exteriorFunctor σ.toAlgHom v =
      (e a) • exteriorFunctor σ.toAlgHom v
    rw [← IsScalarTower.algebraMap_smul F (e a)]
    exact congrArg (fun b : F => b • exteriorFunctor σ.toAlgHom v) (he a).symm

lemma rationalExteriorLinear_wedge (x y : F) :
    rationalExteriorLinear σ e he (rationalWedge k F x y) =
      rationalWedge k F (σ x) (σ y) := by
  change exteriorFunctor σ.toAlgHom _ = _
  simp only [rationalWedge, map_mul, exteriorFunctor_D, AlgEquiv.coe_toAlgHom]

lemma determinantImage_transport :
    (LinearMap.range (determinantMap k A F)).map (rationalExteriorLinear σ e he) =
      LinearMap.range (determinantMap k B F) := by
  rw [determinantMap_generators, determinantMap_generators]
  erw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨fun i => e (a i), ?_⟩
    rw [rationalExteriorLinear_wedge]
    change rationalWedge k F (e (a 0) : F) (e (a 1) : F) = _
    rw [he, he]
    rfl
  · rintro ⟨b,rfl⟩
    refine ⟨rationalWedge k F (e.symm (b 0) : F) (e.symm (b 1) : F), ?_, ?_⟩
    · exact ⟨fun i => e.symm (b i), rfl⟩
    · rw [rationalExteriorLinear_wedge, ← he, ← he, e.apply_symm_apply, e.apply_symm_apply]
      rfl

include he in
lemma determinantImage_transport_frame (w v : ExteriorAlgebra F Ω[F⁄k])
    (hw : LinearMap.range (determinantMap k A F) = Submodule.span A {w})
    (hv : ∃ b : k, b ≠ 0 ∧ exteriorFunctor σ.toAlgHom w = algebraMap k F b • v) :
    LinearMap.range (determinantMap k B F) = Submodule.span B {v} := by
  obtain ⟨b,hb,hv⟩ := hv
  rw [← determinantImage_transport σ e he, hw, Submodule.map_span, Set.image_singleton]
  change Submodule.span B {exteriorFunctor σ.toAlgHom w} = _
  rw [hv]
  have hs : algebraMap k F b • v = (algebraMap k B b) • v := by
    exact (IsScalarTower.algebraMap_smul F (algebraMap k B b) v).symm
  rw [hs]
  exact Submodule.span_singleton_smul_eq ((isUnit_iff_ne_zero.mpr hb).map (algebraMap k B)) v

end CanonicalCoordinates

end

/-! Rational determinant lattices on the twelve smooth affine charts. -/
noncomputable section
open Module KaehlerDifferential CanonicalCoordinates
namespace SourceSymmetry
open ExplicitCone
local instance (A : Subalgebra ℂ L) : Module A Ω[A⁄ℂ] := kaehlerModule ℂ A
local instance (A : Subalgebra ℂ L) : Module A (⋀[A]^2 Ω[A⁄ℂ]) := topModule _ _
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := canonicalExteriorModule _ _

lemma swapChart_coe (t : SectionIndex) (a : coefficientChart t) :
    (swapChart t a : L) = rootSwap (a : L) := rfl
lemma reflectChart_coe (t : SectionIndex) (a : coefficientChart t) :
    (reflectChart t a : L) = rootReflect (a : L) := rfl
lemma invertChart_coe (t : SectionIndex) (a : coefficientChart t) :
    (invertChart t a : L) = rootInvert (a : L) := rfl

lemma canonicalImage_step (t : SectionIndex)
    (ht : LinearMap.range (determinantMap ℂ (coefficientChart t) L) =
      Submodule.span (coefficientChart t) {canonicalDensity t})
    (m : Fin 3) :
    LinearMap.range (determinantMap ℂ (coefficientChart (stepPermutation m t)) L) =
      Submodule.span (coefficientChart (stepPermutation m t))
        {canonicalDensity (stepPermutation m t)} := by
  fin_cases m
  · exact determinantImage_transport_frame rootSwap (swapChart t) (swapChart_coe t)
      _ _ ht (rootSwap_density t)
  · exact determinantImage_transport_frame rootReflect (reflectChart t) (reflectChart_coe t)
      _ _ ht (rootReflect_density t)
  · exact determinantImage_transport_frame rootInvert (invertChart t) (invertChart_coe t)
      _ _ ht (rootInvert_density t)

lemma canonicalImage_word (ms : List (Fin 3)) (t : SectionIndex)
    (ht : LinearMap.range (determinantMap ℂ (coefficientChart t) L) =
      Submodule.span (coefficientChart t) {canonicalDensity t}) :
    LinearMap.range (determinantMap ℂ (coefficientChart (applyWord ms t)) L) =
      Submodule.span (coefficientChart (applyWord ms t))
        {canonicalDensity (applyWord ms t)} := by
  induction ms generalizing t with
  | nil => exact ht
  | cons m ms ih => exact ih _ (canonicalImage_step t ht m)

lemma canonicalImage_congr (t u : SectionIndex) (h : t = u)
    (ht : LinearMap.range (determinantMap ℂ (coefficientChart t) L) =
      Submodule.span (coefficientChart t) {canonicalDensity t}) :
    LinearMap.range (determinantMap ℂ (coefficientChart u) L) =
      Submodule.span (coefficientChart u) {canonicalDensity u} := by
  subst u
  exact ht

/-- The top differential image is the weight-five line lattice on
    every member of the smooth affine cover. -/
lemma coefficientChart_canonicalImage (t : SectionIndex) (ht : Good t) :
    LinearMap.range (determinantMap ℂ (coefficientChart t) L) =
      Submodule.span (coefficientChart t) {canonicalDensity t} := by
  have h := canonicalImage_word (wordFor t) (0,0) sectionChart_canonicalImage
  exact canonicalImage_congr _ t (wordFor_image t ht) h

end SourceSymmetry

end

/-! Exterior algebras of projective modules embed after a faithful scalar extension. -/
noncomputable section
open Module TensorProduct
namespace CanonicalCoordinates
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

lemma exterior_projective [Module.Projective R M] :
    Module.Projective R (ExteriorAlgebra R M) := by
  classical
  obtain ⟨i,hi⟩ := Module.Projective.out (R := R) (P := M)
  let s : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hs : s.comp i = LinearMap.id := LinearMap.ext hi
  let : LinearOrder M := linearOrderOfSTO WellOrderingRel
  let b : Basis M R (M →₀ R) := Finsupp.basisSingleOne
  let : Module.Projective R (ExteriorAlgebra R (M →₀ R)) :=
    Module.Projective.of_basis b.ExteriorAlgebra
  apply Module.Projective.of_split (ExteriorAlgebra.map i).toLinearMap
    (ExteriorAlgebra.map s).toLinearMap
  change ((ExteriorAlgebra.map s).comp (ExteriorAlgebra.map i)).toLinearMap = _
  rw [ExteriorAlgebra.map_comp_map, hs, ExteriorAlgebra.map_id]
  rfl

variable [Invertible (2 : R)]
lemma zero_baseChange : (0 : QuadraticForm R M).baseChange S = 0 := by
  apply baseChange_ext
  intro m
  simp

def exteriorBaseChange :
    ExteriorAlgebra S (S ⊗[R] M) ≃ₐ[S] S ⊗[R] ExteriorAlgebra R M := by
  have h := zero_baseChange R S M
  exact (CliffordAlgebra.equivOfIsometry
    { toLinearEquiv := LinearEquiv.refl S (S ⊗[R] M)
      map_app' := by intro m; rw [h]; rfl }).trans
    (CliffordAlgebra.equivBaseChange S (0 : QuadraticForm R M))

lemma exteriorBaseChange_ι (s : S) (m : M) :
    exteriorBaseChange R S M (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ExteriorAlgebra.ι R m := by
  change CliffordAlgebra.toBaseChange S (0 : QuadraticForm R M)
    (CliffordAlgebra.map _ (CliffordAlgebra.ι _ (s ⊗ₜ[R] m))) = _
  rw [CliffordAlgebra.map_apply_ι]
  exact CliffordAlgebra.toBaseChange_ι S _ s m

end CanonicalCoordinates

end

/-! The top cotangent module of a smooth affine chart embeds in rational forms. -/
noncomputable section
open Module KaehlerDifferential TensorProduct
namespace CanonicalCoordinates
variable (k A F : Type*) [CommRing k] [CommRing A] [CommRing F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]
  [Invertible (2 : A)] [Algebra.FormallyEtale A F]

private def baseChangedExteriorMap :
    F ⊗[A] ExteriorAlgebra A Ω[A⁄k] →ₐ[F] ExteriorAlgebra F Ω[F⁄k] :=
  (ExteriorAlgebra.map
    (tensorKaehlerEquivOfFormallyEtale k A F).toLinearMap).comp
    (exteriorBaseChange A F Ω[A⁄k]).symm.toAlgHom

private lemma baseChangedExteriorMap_injective :
    Function.Injective (baseChangedExteriorMap k A F) := by
  apply Function.Injective.comp _ (exteriorBaseChange A F Ω[A⁄k]).symm.injective
  apply ExteriorAlgebra.map_injective
  use (tensorKaehlerEquivOfFormallyEtale k A F).symm.toLinearMap
  exact (tensorKaehlerEquivOfFormallyEtale k A F).symm_comp

lemma exteriorMap_factorization :
    exteriorMap k A F = ((baseChangedExteriorMap k A F).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : ExteriorAlgebra A Ω[A⁄k] →ₐ[A]
        F ⊗[A] ExteriorAlgebra A Ω[A⁄k]) := by
  apply ExteriorAlgebra.hom_ext
  ext a
  change exteriorMap k A F (ExteriorAlgebra.ι A (D k A a)) =
    baseChangedExteriorMap k A F (1 ⊗ₜ[A] ExteriorAlgebra.ι A (D k A a))
  rw [exteriorMap_D]
  have h := exteriorBaseChange_ι A F Ω[A⁄k] (1 : F) (D k A a)
  rw [← h]
  simp only [baseChangedExteriorMap, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, ExteriorAlgebra.map_apply_ι,
    LinearEquiv.coe_coe, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, map_D]

variable [Algebra.FormallySmooth k A] [FaithfulSMul A F]

lemma exteriorMap_injective : Function.Injective (exteriorMap k A F) := by
  have := exterior_projective A Ω[A⁄k]
  rw [exteriorMap_factorization]
  apply Function.Injective.comp (baseChangedExteriorMap_injective k A F)
  exact Module.Flat.tensorProduct_mk_injective A (ExteriorAlgebra A Ω[A⁄k]) F

lemma determinantMap_injective : Function.Injective (determinantMap k A F) :=
  (exteriorMap_injective k A F).comp Subtype.val_injective

end CanonicalCoordinates

end

/-! Identification of a top differential module by a nonzero rational frame. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
variable (k A F : Type*) [CommRing k] [CommRing A] [IsDomain A] [Field F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]
  [Invertible (2 : A)] [Algebra.FormallySmooth k A]
  [Algebra.FormallyEtale A F] [FaithfulSMul A F]
local instance : Module.IsTorsionFree A (ExteriorAlgebra F Ω[F⁄k]) :=
  Module.IsTorsionFree.trans F

variable (w : ExteriorAlgebra F Ω[F⁄k])
  (hw : LinearMap.range (determinantMap k A F) = Submodule.span A {w}) (hn : w ≠ 0)

def determinantTrivialization : (⋀[A]^2 Ω[A⁄k]) ≃ₗ[A] A :=
  (LinearEquiv.ofInjective (determinantMap k A F) (determinantMap_injective k A F)).trans
    ((LinearEquiv.ofEq _ _ hw).trans (LinearEquiv.toSpanNonzeroSingleton A _ w hn).symm)

lemma determinantTrivialization_spec (m : ⋀[A]^2 Ω[A⁄k]) :
    determinantMap k A F m = determinantTrivialization k A F w hw hn m • w := by
  exact (LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul A
    (ExteriorAlgebra F Ω[F⁄k]) w hn
      ((LinearEquiv.ofEq _ _ hw) (⟨determinantMap k A F m, LinearMap.mem_range_self _ m⟩))).symm

lemma determinantTrivialization_symm_spec (a : A) :
    determinantMap k A F ((determinantTrivialization k A F w hw hn).symm a) = a • w := by
  rw [determinantTrivialization_spec k A F w hw hn, LinearEquiv.apply_symm_apply]

end CanonicalCoordinates

end

/-! Canonical modules and their generators on the smooth affine charts. -/
noncomputable section
open Module KaehlerDifferential CanonicalCoordinates
open scoped nonZeroDivisors
namespace CanonicalCoordinates
@[instance_reducible] def selfModule (A : Type*) [CommRing A] : Module A A := inferInstance
theorem subalgebraDomain (k F : Type*) [CommRing k] [Field F]
    [Algebra k F] (A : Subalgebra k F) : IsDomain A := inferInstance
theorem subalgebraTower (k F : Type*) [CommRing k] [Field F]
    [Algebra k F] (A : Subalgebra k F) : IsScalarTower k A F := inferInstance
theorem subalgebraFaithful (k F : Type*) [CommRing k] [Field F]
    [Algebra k F] (A : Subalgebra k F) : FaithfulSMul A F := inferInstance
end CanonicalCoordinates
namespace SourceSymmetry
open ExplicitCone
local instance (A : Subalgebra ℂ L) : Module A Ω[A⁄ℂ] := kaehlerModule ℂ A
local instance (A : Subalgebra ℂ L) : Module A (⋀[A]^2 Ω[A⁄ℂ]) := topModule _ _
local instance (A : Subalgebra ℂ L) : SMul A (⋀[A]^2 Ω[A⁄ℂ]) := (topModule _ _).toSMul
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := canonicalExteriorModule _ _
local instance : SMul L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorSMul _ _
local instance : MulAction L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra L (ExteriorAlgebra L Ω[L⁄ℂ]) := rationalExteriorAlgebra _ _
local instance (A : Subalgebra ℂ L) : IsScalarTower A L (ExteriorAlgebra L Ω[L⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
local instance (A : Subalgebra ℂ L) : Module A A := selfModule A
local instance (A : Subalgebra ℂ L) : IsDomain A := subalgebraDomain ℂ L A
local instance (A : Subalgebra ℂ L) : IsScalarTower ℂ A L := subalgebraTower ℂ L A
local instance (A : Subalgebra ℂ L) : FaithfulSMul A L := subalgebraFaithful ℂ L A
local instance (A : Subalgebra ℂ L) : Invertible (2 : A) := by
  have h : IsUnit (2 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h' : IsUnit (2 : A) := by simpa only [map_ofNat] using h.map (algebraMap ℂ A)
  exact h'.invertible
local instance (t : SectionIndex) : Algebra.FormallyEtale (coefficientChart t) L :=
  Algebra.FormallyEtale.of_isLocalization (coefficientChart t)⁰

/-- A frame of the top cotangent module on every good affine open. -/
def coefficientCanonicalFrame (t : SectionIndex) (ht : Good t) :
    (⋀[coefficientChart t]^2 Ω[coefficientChart t⁄ℂ]) ≃ₗ[coefficientChart t]
      coefficientChart t := by
  letI := coefficientChart_smooth t ht
  exact determinantTrivialization ℂ (coefficientChart t) L (canonicalDensity t)
    (coefficientChart_canonicalImage t ht) (canonicalDensity_ne_zero t)

lemma coefficientCanonicalFrame_spec (t : SectionIndex) (ht : Good t)
    (m : ⋀[coefficientChart t]^2 Ω[coefficientChart t⁄ℂ]) :
    determinantMap ℂ (coefficientChart t) L m =
      coefficientCanonicalFrame t ht m • canonicalDensity t := by
  let := coefficientChart_smooth t ht
  exact determinantTrivialization_spec ℂ (coefficientChart t) L (canonicalDensity t)
    (coefficientChart_canonicalImage t ht) (canonicalDensity_ne_zero t) m

/-- A generator of the top differential module. -/
def coefficientCanonicalGenerator (t : SectionIndex) (ht : Good t) :
    ⋀[coefficientChart t]^2 Ω[coefficientChart t⁄ℂ] :=
  (coefficientCanonicalFrame t ht).symm 1

lemma coefficientCanonicalGenerator_spec (t : SectionIndex) (ht : Good t) :
    determinantMap ℂ (coefficientChart t) L (coefficientCanonicalGenerator t ht) =
      canonicalDensity t := by
  rw [coefficientCanonicalFrame_spec t ht]
  simp only [coefficientCanonicalGenerator, LinearEquiv.apply_symm_apply, one_smul]

lemma coefficientCanonicalGenerator_transition (s t : SectionIndex)
    (hs : Good s) (ht : Good t) :
    determinantMap ℂ (coefficientChart s) L (coefficientCanonicalGenerator s hs) =
      (sectionCoefficient s / sectionCoefficient t)^5 •
        determinantMap ℂ (coefficientChart t) L (coefficientCanonicalGenerator t ht) := by
  have hs' := coefficientCanonicalGenerator_spec s hs
  have ht' := coefficientCanonicalGenerator_spec t ht
  exact hs'.trans ((canonicalDensity_ratio s t).trans
    (congrArg (fun v => (sectionCoefficient s / sectionCoefficient t)^5 • v) ht'.symm))

end SourceSymmetry

end

end OAI
